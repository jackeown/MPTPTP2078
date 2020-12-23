%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:58 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 236 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 ( 519 expanded)
%              Number of equality atoms :  109 ( 302 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f598,f604,f1019,f1030])).

fof(f1030,plain,
    ( spl7_2
    | ~ spl7_50 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | spl7_2
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f1028,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1028,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f1027,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f89,f149])).

fof(f149,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f114,f148])).

fof(f148,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f115,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f128,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f137,f145])).

fof(f145,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f139,f144])).

fof(f144,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f140,f141])).

fof(f141,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f137,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f128,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f115,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f114,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1027,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f1026,f171])).

fof(f171,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1026,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f1021,f995])).

fof(f995,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f527,f85])).

fof(f85,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f39])).

fof(f39,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f527,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f526,f88])).

fof(f88,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f526,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f525,f186])).

fof(f186,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f111,f171])).

fof(f111,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f525,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f511,f205])).

fof(f205,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f157,f152])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f90,f113])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f157,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f124,f113])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f511,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f101,f87])).

fof(f87,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f1021,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | ~ spl7_50 ),
    inference(resolution,[],[f1003,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f97,f149])).

fof(f97,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f1003,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1002,plain,
    ( spl7_50
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f1019,plain,(
    spl7_50 ),
    inference(avatar_contradiction_clause,[],[f1018])).

fof(f1018,plain,
    ( $false
    | spl7_50 ),
    inference(subsumption_resolution,[],[f1017,f85])).

fof(f1017,plain,
    ( ~ v1_relat_1(sK0)
    | spl7_50 ),
    inference(subsumption_resolution,[],[f1016,f186])).

fof(f1016,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl7_50 ),
    inference(resolution,[],[f1004,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1004,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl7_50 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f604,plain,
    ( spl7_1
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl7_1
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f592,f581])).

fof(f581,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl7_27
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f592,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f591,f263])).

fof(f263,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f254,f205])).

fof(f254,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
    | spl7_1 ),
    inference(extensionality_resolution,[],[f120,f180])).

fof(f180,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f591,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f577,f172])).

fof(f172,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f577,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f96,f573])).

fof(f573,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f467,f85])).

fof(f467,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f466,f87])).

fof(f466,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f465,f186])).

fof(f465,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f452,f205])).

fof(f452,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f100,f88])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f96,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f598,plain,(
    spl7_27 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | spl7_27 ),
    inference(subsumption_resolution,[],[f596,f186])).

fof(f596,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_27 ),
    inference(subsumption_resolution,[],[f595,f85])).

fof(f595,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_27 ),
    inference(resolution,[],[f582,f117])).

fof(f582,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f580])).

fof(f185,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f86,f182,f178])).

fof(f86,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (25539)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (25548)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.26/0.52  % (25547)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.26/0.52  % (25541)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  % (25559)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.53  % (25558)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.53  % (25535)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (25536)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (25550)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (25549)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.53  % (25561)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.26/0.53  % (25544)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.26/0.53  % (25537)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.53  % (25552)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.54  % (25538)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.54  % (25542)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.54  % (25557)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.54  % (25560)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.54  % (25556)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.54  % (25562)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (25553)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.55  % (25545)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.55  % (25551)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (25546)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (25563)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  % (25564)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.55  % (25545)Refutation not found, incomplete strategy% (25545)------------------------------
% 1.42/0.55  % (25545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (25545)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (25545)Memory used [KB]: 10746
% 1.42/0.55  % (25545)Time elapsed: 0.139 s
% 1.42/0.55  % (25545)------------------------------
% 1.42/0.55  % (25545)------------------------------
% 1.42/0.55  % (25534)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.55  % (25564)Refutation not found, incomplete strategy% (25564)------------------------------
% 1.42/0.55  % (25564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (25564)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (25564)Memory used [KB]: 10746
% 1.42/0.55  % (25564)Time elapsed: 0.145 s
% 1.42/0.55  % (25564)------------------------------
% 1.42/0.55  % (25564)------------------------------
% 1.42/0.55  % (25555)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.56  % (25543)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.56  % (25565)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.57  % (25541)Refutation found. Thanks to Tanya!
% 1.42/0.57  % SZS status Theorem for theBenchmark
% 1.42/0.57  % SZS output start Proof for theBenchmark
% 1.42/0.57  fof(f1032,plain,(
% 1.42/0.57    $false),
% 1.42/0.57    inference(avatar_sat_refutation,[],[f185,f598,f604,f1019,f1030])).
% 1.42/0.57  fof(f1030,plain,(
% 1.42/0.57    spl7_2 | ~spl7_50),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f1029])).
% 1.42/0.57  fof(f1029,plain,(
% 1.42/0.57    $false | (spl7_2 | ~spl7_50)),
% 1.42/0.57    inference(subsumption_resolution,[],[f1028,f184])).
% 1.42/0.57  fof(f184,plain,(
% 1.42/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl7_2),
% 1.42/0.57    inference(avatar_component_clause,[],[f182])).
% 1.42/0.57  fof(f182,plain,(
% 1.42/0.57    spl7_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.42/0.57  fof(f1028,plain,(
% 1.42/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl7_50),
% 1.42/0.57    inference(forward_demodulation,[],[f1027,f151])).
% 1.42/0.57  fof(f151,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f89,f149])).
% 1.42/0.57  fof(f149,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f114,f148])).
% 1.42/0.57  fof(f148,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f115,f147])).
% 1.42/0.57  fof(f147,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f128,f146])).
% 1.42/0.57  fof(f146,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f137,f145])).
% 1.42/0.57  fof(f145,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f139,f144])).
% 1.42/0.57  fof(f144,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f140,f141])).
% 1.42/0.57  fof(f141,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f16])).
% 1.42/0.57  fof(f16,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.42/0.57  fof(f140,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f15])).
% 1.42/0.57  fof(f15,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.42/0.57  fof(f139,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f14])).
% 1.42/0.57  fof(f14,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.42/0.57  fof(f137,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f13])).
% 1.42/0.57  fof(f13,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.57  fof(f128,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f12])).
% 1.42/0.57  fof(f12,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.57  fof(f115,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f11])).
% 1.42/0.57  fof(f11,axiom,(
% 1.42/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.57  fof(f114,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f23])).
% 1.42/0.57  fof(f23,axiom,(
% 1.42/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.57  fof(f89,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f5])).
% 1.42/0.57  fof(f5,axiom,(
% 1.42/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.42/0.57  fof(f1027,plain,(
% 1.42/0.57    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | ~spl7_50),
% 1.42/0.57    inference(forward_demodulation,[],[f1026,f171])).
% 1.42/0.57  fof(f171,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.42/0.57    inference(equality_resolution,[],[f123])).
% 1.42/0.57  fof(f123,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.42/0.57    inference(cnf_transformation,[],[f78])).
% 1.42/0.57  fof(f78,plain,(
% 1.42/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.57    inference(flattening,[],[f77])).
% 1.42/0.57  fof(f77,plain,(
% 1.42/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.57    inference(nnf_transformation,[],[f17])).
% 1.42/0.57  fof(f17,axiom,(
% 1.42/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.42/0.57  fof(f1026,plain,(
% 1.42/0.57    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | ~spl7_50),
% 1.42/0.57    inference(forward_demodulation,[],[f1021,f995])).
% 1.42/0.57  fof(f995,plain,(
% 1.42/0.57    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.42/0.57    inference(resolution,[],[f527,f85])).
% 1.42/0.57  fof(f85,plain,(
% 1.42/0.57    v1_relat_1(sK0)),
% 1.42/0.57    inference(cnf_transformation,[],[f65])).
% 1.42/0.57  fof(f65,plain,(
% 1.42/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.42/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f64])).
% 1.42/0.57  fof(f64,plain,(
% 1.42/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.42/0.57    introduced(choice_axiom,[])).
% 1.42/0.57  fof(f42,plain,(
% 1.42/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f40])).
% 1.42/0.57  fof(f40,negated_conjecture,(
% 1.42/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.42/0.57    inference(negated_conjecture,[],[f39])).
% 1.42/0.57  fof(f39,conjecture,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.42/0.57  fof(f527,plain,(
% 1.42/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.42/0.57    inference(forward_demodulation,[],[f526,f88])).
% 1.42/0.57  fof(f88,plain,(
% 1.42/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.42/0.57    inference(cnf_transformation,[],[f38])).
% 1.42/0.57  fof(f38,axiom,(
% 1.42/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.42/0.57  fof(f526,plain,(
% 1.42/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f525,f186])).
% 1.42/0.57  fof(f186,plain,(
% 1.42/0.57    v1_relat_1(k1_xboole_0)),
% 1.42/0.57    inference(superposition,[],[f111,f171])).
% 1.42/0.57  fof(f111,plain,(
% 1.42/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f28])).
% 1.42/0.57  fof(f28,axiom,(
% 1.42/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.42/0.57  fof(f525,plain,(
% 1.42/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f511,f205])).
% 1.42/0.57  fof(f205,plain,(
% 1.42/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.57    inference(trivial_inequality_removal,[],[f204])).
% 1.42/0.57  fof(f204,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.57    inference(superposition,[],[f157,f152])).
% 1.42/0.57  fof(f152,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f90,f113])).
% 1.42/0.57  fof(f113,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f22])).
% 1.42/0.57  fof(f22,axiom,(
% 1.42/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.42/0.57  fof(f90,plain,(
% 1.42/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f6])).
% 1.42/0.57  fof(f6,axiom,(
% 1.42/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.42/0.57  fof(f157,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f124,f113])).
% 1.42/0.57  fof(f124,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.42/0.57    inference(cnf_transformation,[],[f79])).
% 1.42/0.57  fof(f79,plain,(
% 1.42/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.42/0.57    inference(nnf_transformation,[],[f3])).
% 1.42/0.57  fof(f3,axiom,(
% 1.42/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.42/0.57  fof(f511,plain,(
% 1.42/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.42/0.57    inference(superposition,[],[f101,f87])).
% 1.42/0.57  fof(f87,plain,(
% 1.42/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.57    inference(cnf_transformation,[],[f38])).
% 1.42/0.57  fof(f101,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f51])).
% 1.42/0.57  fof(f51,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(flattening,[],[f50])).
% 1.42/0.57  fof(f50,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f34])).
% 1.42/0.57  fof(f34,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.42/0.57  fof(f1021,plain,(
% 1.42/0.57    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) | ~spl7_50),
% 1.42/0.57    inference(resolution,[],[f1003,f153])).
% 1.42/0.57  fof(f153,plain,(
% 1.42/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.42/0.57    inference(definition_unfolding,[],[f97,f149])).
% 1.42/0.57  fof(f97,plain,(
% 1.42/0.57    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f46])).
% 1.42/0.57  fof(f46,plain,(
% 1.42/0.57    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f31])).
% 1.42/0.57  fof(f31,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.42/0.57  fof(f1003,plain,(
% 1.42/0.57    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl7_50),
% 1.42/0.57    inference(avatar_component_clause,[],[f1002])).
% 1.42/0.57  fof(f1002,plain,(
% 1.42/0.57    spl7_50 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 1.42/0.57  fof(f1019,plain,(
% 1.42/0.57    spl7_50),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f1018])).
% 1.42/0.57  fof(f1018,plain,(
% 1.42/0.57    $false | spl7_50),
% 1.42/0.57    inference(subsumption_resolution,[],[f1017,f85])).
% 1.42/0.57  fof(f1017,plain,(
% 1.42/0.57    ~v1_relat_1(sK0) | spl7_50),
% 1.42/0.57    inference(subsumption_resolution,[],[f1016,f186])).
% 1.42/0.57  fof(f1016,plain,(
% 1.42/0.57    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl7_50),
% 1.42/0.57    inference(resolution,[],[f1004,f117])).
% 1.42/0.57  fof(f117,plain,(
% 1.42/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f60])).
% 1.42/0.57  fof(f60,plain,(
% 1.42/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(flattening,[],[f59])).
% 1.42/0.57  fof(f59,plain,(
% 1.42/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.42/0.57    inference(ennf_transformation,[],[f27])).
% 1.42/0.57  fof(f27,axiom,(
% 1.42/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.42/0.57  fof(f1004,plain,(
% 1.42/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl7_50),
% 1.42/0.57    inference(avatar_component_clause,[],[f1002])).
% 1.42/0.57  fof(f604,plain,(
% 1.42/0.57    spl7_1 | ~spl7_27),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f603])).
% 1.42/0.57  fof(f603,plain,(
% 1.42/0.57    $false | (spl7_1 | ~spl7_27)),
% 1.42/0.57    inference(subsumption_resolution,[],[f592,f581])).
% 1.42/0.57  fof(f581,plain,(
% 1.42/0.57    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_27),
% 1.42/0.57    inference(avatar_component_clause,[],[f580])).
% 1.42/0.57  fof(f580,plain,(
% 1.42/0.57    spl7_27 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.42/0.57  fof(f592,plain,(
% 1.42/0.57    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl7_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f591,f263])).
% 1.42/0.57  fof(f263,plain,(
% 1.42/0.57    ~r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | spl7_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f254,f205])).
% 1.42/0.57  fof(f254,plain,(
% 1.42/0.57    ~r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) | spl7_1),
% 1.42/0.57    inference(extensionality_resolution,[],[f120,f180])).
% 1.42/0.57  fof(f180,plain,(
% 1.42/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl7_1),
% 1.42/0.57    inference(avatar_component_clause,[],[f178])).
% 1.42/0.57  fof(f178,plain,(
% 1.42/0.57    spl7_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.42/0.57  fof(f120,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f76])).
% 1.42/0.57  fof(f76,plain,(
% 1.42/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.57    inference(flattening,[],[f75])).
% 1.42/0.57  fof(f75,plain,(
% 1.42/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.57    inference(nnf_transformation,[],[f2])).
% 1.42/0.57  fof(f2,axiom,(
% 1.42/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.57  fof(f591,plain,(
% 1.42/0.57    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.42/0.57    inference(forward_demodulation,[],[f577,f172])).
% 1.42/0.57  fof(f172,plain,(
% 1.42/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.42/0.57    inference(equality_resolution,[],[f122])).
% 1.42/0.57  fof(f122,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.42/0.57    inference(cnf_transformation,[],[f78])).
% 1.42/0.57  fof(f577,plain,(
% 1.42/0.57    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.42/0.57    inference(superposition,[],[f96,f573])).
% 1.42/0.57  fof(f573,plain,(
% 1.42/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.42/0.57    inference(resolution,[],[f467,f85])).
% 1.42/0.57  fof(f467,plain,(
% 1.42/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.42/0.57    inference(forward_demodulation,[],[f466,f87])).
% 1.42/0.57  fof(f466,plain,(
% 1.42/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f465,f186])).
% 1.42/0.57  fof(f465,plain,(
% 1.42/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f452,f205])).
% 1.42/0.57  fof(f452,plain,(
% 1.42/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.42/0.57    inference(superposition,[],[f100,f88])).
% 1.42/0.57  fof(f100,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f49])).
% 1.42/0.57  fof(f49,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(flattening,[],[f48])).
% 1.42/0.57  fof(f48,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f33])).
% 1.42/0.57  fof(f33,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.42/0.57  fof(f96,plain,(
% 1.42/0.57    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f45])).
% 1.42/0.57  fof(f45,plain,(
% 1.42/0.57    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f30])).
% 1.42/0.57  fof(f30,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.42/0.57  fof(f598,plain,(
% 1.42/0.57    spl7_27),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f597])).
% 1.42/0.57  fof(f597,plain,(
% 1.42/0.57    $false | spl7_27),
% 1.42/0.57    inference(subsumption_resolution,[],[f596,f186])).
% 1.42/0.57  fof(f596,plain,(
% 1.42/0.57    ~v1_relat_1(k1_xboole_0) | spl7_27),
% 1.42/0.57    inference(subsumption_resolution,[],[f595,f85])).
% 1.42/0.57  fof(f595,plain,(
% 1.42/0.57    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl7_27),
% 1.42/0.57    inference(resolution,[],[f582,f117])).
% 1.42/0.57  fof(f582,plain,(
% 1.42/0.57    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl7_27),
% 1.42/0.57    inference(avatar_component_clause,[],[f580])).
% 1.42/0.57  fof(f185,plain,(
% 1.42/0.57    ~spl7_1 | ~spl7_2),
% 1.42/0.57    inference(avatar_split_clause,[],[f86,f182,f178])).
% 1.42/0.57  fof(f86,plain,(
% 1.42/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.42/0.57    inference(cnf_transformation,[],[f65])).
% 1.42/0.57  % SZS output end Proof for theBenchmark
% 1.42/0.57  % (25541)------------------------------
% 1.42/0.57  % (25541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (25541)Termination reason: Refutation
% 1.42/0.57  
% 1.42/0.57  % (25541)Memory used [KB]: 11257
% 1.42/0.57  % (25541)Time elapsed: 0.161 s
% 1.42/0.57  % (25541)------------------------------
% 1.42/0.57  % (25541)------------------------------
% 1.42/0.57  % (25551)Refutation not found, incomplete strategy% (25551)------------------------------
% 1.42/0.57  % (25551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (25551)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (25551)Memory used [KB]: 10746
% 1.42/0.57  % (25551)Time elapsed: 0.164 s
% 1.42/0.57  % (25551)------------------------------
% 1.42/0.57  % (25551)------------------------------
% 1.42/0.59  % (25531)Success in time 0.23 s
%------------------------------------------------------------------------------
