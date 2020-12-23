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
% DateTime   : Thu Dec  3 12:47:53 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 612 expanded)
%              Number of leaves         :   31 ( 190 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 ( 966 expanded)
%              Number of equality atoms :  108 ( 501 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f925,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f189,f296,f318,f385,f845,f924])).

fof(f924,plain,
    ( spl1_2
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f923])).

fof(f923,plain,
    ( $false
    | spl1_2
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f106,f798])).

fof(f798,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f775,f431])).

fof(f431,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f429,f430])).

fof(f430,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f411,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f411,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f75,f74])).

fof(f74,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f59,f71])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f429,plain,(
    k4_relat_1(k1_xboole_0) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f413,f49])).

fof(f413,plain,(
    k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f132,f410])).

fof(f410,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f75,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f132,plain,(
    k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f118,f76])).

fof(f76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f55,f76])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f775,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f169,f774])).

fof(f774,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f773,f72])).

fof(f773,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f772,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f772,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))))
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f759,f741])).

fof(f741,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f615,f738])).

fof(f738,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f731,f697])).

fof(f697,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f683,f431])).

fof(f683,plain,
    ( k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_11 ),
    inference(resolution,[],[f309,f76])).

fof(f309,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X1,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X1)) )
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f299,f83])).

fof(f83,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f299,plain,
    ( ! [X1] :
        ( k4_relat_1(k5_relat_1(X1,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_11 ),
    inference(resolution,[],[f283,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f283,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl1_11
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f731,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_11 ),
    inference(resolution,[],[f164,f283])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f90,f76])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f64,f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f615,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_11 ),
    inference(resolution,[],[f606,f283])).

fof(f606,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f605,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f605,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f604,f76])).

fof(f604,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f602,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f602,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f57,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f759,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))))
    | ~ spl1_7 ),
    inference(resolution,[],[f73,f178])).

fof(f178,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl1_7
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f54,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f169,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f168,f76])).

fof(f168,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    inference(resolution,[],[f90,f42])).

fof(f106,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f845,plain,
    ( spl1_1
    | ~ spl1_18 ),
    inference(avatar_contradiction_clause,[],[f844])).

fof(f844,plain,
    ( $false
    | spl1_1
    | ~ spl1_18 ),
    inference(subsumption_resolution,[],[f843,f102])).

fof(f102,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f843,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f842,f72])).

fof(f842,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f841,f86])).

fof(f841,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f767,f621])).

fof(f621,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f606,f42])).

fof(f767,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl1_18 ),
    inference(resolution,[],[f73,f444])).

fof(f444,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_18 ),
    inference(backward_demodulation,[],[f375,f431])).

fof(f375,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl1_18
  <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f385,plain,
    ( ~ spl1_12
    | spl1_18 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl1_12
    | spl1_18 ),
    inference(subsumption_resolution,[],[f383,f287])).

fof(f287,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl1_12
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f383,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_18 ),
    inference(subsumption_resolution,[],[f382,f42])).

fof(f382,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_18 ),
    inference(resolution,[],[f376,f64])).

fof(f376,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | spl1_18 ),
    inference(avatar_component_clause,[],[f374])).

fof(f318,plain,(
    spl1_12 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl1_12 ),
    inference(subsumption_resolution,[],[f316,f76])).

fof(f316,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_12 ),
    inference(resolution,[],[f288,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f288,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f286])).

fof(f296,plain,(
    spl1_11 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl1_11 ),
    inference(subsumption_resolution,[],[f294,f42])).

fof(f294,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_11 ),
    inference(resolution,[],[f284,f52])).

fof(f284,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_11 ),
    inference(avatar_component_clause,[],[f282])).

fof(f189,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl1_7 ),
    inference(subsumption_resolution,[],[f187,f42])).

fof(f187,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(subsumption_resolution,[],[f186,f76])).

fof(f186,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(resolution,[],[f185,f64])).

fof(f185,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_7 ),
    inference(resolution,[],[f179,f52])).

fof(f179,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f107,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f43,f104,f100])).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (8710)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (8698)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (8708)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (8711)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (8702)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (8709)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (8703)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (8707)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (8705)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (8706)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (8715)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (8712)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (8700)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (8701)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (8714)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (8699)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (8713)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.44/0.53  % (8704)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.44/0.54  % (8707)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f925,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(avatar_sat_refutation,[],[f107,f189,f296,f318,f385,f845,f924])).
% 1.44/0.54  fof(f924,plain,(
% 1.44/0.54    spl1_2 | ~spl1_7 | ~spl1_11),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f923])).
% 1.44/0.54  fof(f923,plain,(
% 1.44/0.54    $false | (spl1_2 | ~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(subsumption_resolution,[],[f106,f798])).
% 1.44/0.54  fof(f798,plain,(
% 1.44/0.54    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f775,f431])).
% 1.44/0.54  fof(f431,plain,(
% 1.44/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.44/0.54    inference(backward_demodulation,[],[f429,f430])).
% 1.44/0.54  fof(f430,plain,(
% 1.44/0.54    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 1.44/0.54    inference(forward_demodulation,[],[f411,f49])).
% 1.44/0.54  fof(f49,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f7])).
% 1.44/0.54  fof(f7,axiom,(
% 1.44/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.44/0.54  fof(f411,plain,(
% 1.44/0.54    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.44/0.54    inference(superposition,[],[f75,f74])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.44/0.54    inference(definition_unfolding,[],[f58,f71])).
% 1.44/0.54  fof(f71,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.54    inference(definition_unfolding,[],[f60,f70])).
% 1.44/0.54  fof(f70,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.44/0.54    inference(definition_unfolding,[],[f61,f69])).
% 1.44/0.54  fof(f69,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.44/0.54    inference(definition_unfolding,[],[f65,f68])).
% 1.44/0.54  fof(f68,plain,(
% 1.44/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.44/0.54    inference(definition_unfolding,[],[f66,f67])).
% 1.44/0.54  fof(f67,plain,(
% 1.44/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f11])).
% 1.44/0.54  fof(f11,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.44/0.54  fof(f66,plain,(
% 1.44/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,axiom,(
% 1.44/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.54  fof(f65,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f9])).
% 1.44/0.54  fof(f9,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.54  fof(f61,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.54  fof(f60,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f14])).
% 1.44/0.54  fof(f14,axiom,(
% 1.44/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.54    inference(rectify,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.44/0.54  fof(f75,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.44/0.54    inference(definition_unfolding,[],[f62,f59,f71])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f13])).
% 1.44/0.54  fof(f13,axiom,(
% 1.44/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.44/0.54  fof(f62,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.54  fof(f429,plain,(
% 1.44/0.54    k4_relat_1(k1_xboole_0) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))),
% 1.44/0.54    inference(forward_demodulation,[],[f413,f49])).
% 1.44/0.54  fof(f413,plain,(
% 1.44/0.54    k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.44/0.54    inference(backward_demodulation,[],[f132,f410])).
% 1.44/0.54  fof(f410,plain,(
% 1.44/0.54    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.54    inference(superposition,[],[f75,f72])).
% 1.44/0.54  fof(f72,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.44/0.54    inference(definition_unfolding,[],[f48,f71])).
% 1.44/0.54  fof(f48,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.54  fof(f132,plain,(
% 1.44/0.54    k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))),
% 1.44/0.54    inference(resolution,[],[f118,f76])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    v1_relat_1(k1_xboole_0)),
% 1.44/0.54    inference(resolution,[],[f50,f44])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    v1_xboole_0(k1_xboole_0)),
% 1.44/0.54    inference(cnf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    v1_xboole_0(k1_xboole_0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f15])).
% 1.44/0.54  fof(f15,axiom,(
% 1.44/0.54    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.44/0.54  fof(f118,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))) )),
% 1.44/0.54    inference(resolution,[],[f55,f76])).
% 1.44/0.54  fof(f55,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f20])).
% 1.44/0.54  fof(f20,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 1.44/0.54  fof(f775,plain,(
% 1.44/0.54    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(backward_demodulation,[],[f169,f774])).
% 1.44/0.54  fof(f774,plain,(
% 1.44/0.54    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f773,f72])).
% 1.44/0.54  fof(f773,plain,(
% 1.44/0.54    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | (~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f772,f86])).
% 1.44/0.54  fof(f86,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.44/0.54    inference(resolution,[],[f78,f44])).
% 1.44/0.54  fof(f78,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.44/0.54    inference(resolution,[],[f63,f51])).
% 1.44/0.54  fof(f51,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f3])).
% 1.44/0.54  fof(f3,axiom,(
% 1.44/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f37])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f12])).
% 1.44/0.54  fof(f12,axiom,(
% 1.44/0.54    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.44/0.54  fof(f772,plain,(
% 1.44/0.54    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) | (~spl1_7 | ~spl1_11)),
% 1.44/0.54    inference(forward_demodulation,[],[f759,f741])).
% 1.44/0.54  fof(f741,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_11),
% 1.44/0.54    inference(backward_demodulation,[],[f615,f738])).
% 1.44/0.54  fof(f738,plain,(
% 1.44/0.54    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_11),
% 1.44/0.54    inference(forward_demodulation,[],[f731,f697])).
% 1.44/0.54  fof(f697,plain,(
% 1.44/0.54    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_11),
% 1.44/0.54    inference(forward_demodulation,[],[f683,f431])).
% 1.44/0.54  fof(f683,plain,(
% 1.44/0.54    k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_11),
% 1.44/0.54    inference(resolution,[],[f309,f76])).
% 1.44/0.54  fof(f309,plain,(
% 1.44/0.54    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X1))) ) | ~spl1_11),
% 1.44/0.54    inference(forward_demodulation,[],[f299,f83])).
% 1.44/0.54  fof(f83,plain,(
% 1.44/0.54    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 1.44/0.54    inference(resolution,[],[f53,f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    v1_relat_1(sK0)),
% 1.44/0.54    inference(cnf_transformation,[],[f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f40])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f25])).
% 1.44/0.54  fof(f25,negated_conjecture,(
% 1.44/0.54    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.54    inference(negated_conjecture,[],[f24])).
% 1.44/0.54  fof(f24,conjecture,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.44/0.54  fof(f53,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f18])).
% 1.44/0.54  fof(f18,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.44/0.54  fof(f299,plain,(
% 1.44/0.54    ( ! [X1] : (k4_relat_1(k5_relat_1(X1,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_11),
% 1.44/0.54    inference(resolution,[],[f283,f56])).
% 1.44/0.54  fof(f56,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f22])).
% 1.44/0.54  fof(f22,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.44/0.54  fof(f283,plain,(
% 1.44/0.54    v1_relat_1(k4_relat_1(sK0)) | ~spl1_11),
% 1.44/0.54    inference(avatar_component_clause,[],[f282])).
% 1.44/0.54  fof(f282,plain,(
% 1.44/0.54    spl1_11 <=> v1_relat_1(k4_relat_1(sK0))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.44/0.54  fof(f731,plain,(
% 1.44/0.54    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | ~spl1_11),
% 1.44/0.54    inference(resolution,[],[f164,f283])).
% 1.44/0.54  fof(f164,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0)))) )),
% 1.44/0.54    inference(resolution,[],[f90,f76])).
% 1.44/0.54  fof(f90,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 1.44/0.54    inference(resolution,[],[f64,f53])).
% 1.44/0.54  fof(f64,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f38])).
% 1.44/0.54  fof(f38,plain,(
% 1.44/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f17])).
% 1.44/0.54  fof(f17,axiom,(
% 1.44/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.44/0.54  fof(f615,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_11),
% 1.44/0.54    inference(resolution,[],[f606,f283])).
% 1.44/0.54  fof(f606,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.44/0.54    inference(forward_demodulation,[],[f605,f45])).
% 1.44/0.54  fof(f45,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.54    inference(cnf_transformation,[],[f23])).
% 1.44/0.54  fof(f23,axiom,(
% 1.44/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.54  fof(f605,plain,(
% 1.44/0.54    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f604,f76])).
% 1.44/0.54  fof(f604,plain,(
% 1.44/0.54    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f602,f47])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.54  fof(f602,plain,(
% 1.44/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.44/0.54    inference(superposition,[],[f57,f46])).
% 1.44/0.54  fof(f46,plain,(
% 1.44/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.54    inference(cnf_transformation,[],[f23])).
% 1.44/0.54  fof(f57,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f36])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f35])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f21])).
% 1.44/0.54  fof(f21,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.44/0.54  fof(f759,plain,(
% 1.44/0.54    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) | ~spl1_7),
% 1.44/0.54    inference(resolution,[],[f73,f178])).
% 1.44/0.54  fof(f178,plain,(
% 1.44/0.54    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f177])).
% 1.44/0.54  fof(f177,plain,(
% 1.44/0.54    spl1_7 <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.44/0.54  fof(f73,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.44/0.54    inference(definition_unfolding,[],[f54,f71])).
% 1.44/0.54  fof(f54,plain,(
% 1.44/0.54    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f19])).
% 1.44/0.54  fof(f19,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.44/0.54  fof(f169,plain,(
% 1.44/0.54    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.44/0.54    inference(resolution,[],[f168,f76])).
% 1.44/0.54  fof(f168,plain,(
% 1.44/0.54    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) )),
% 1.44/0.54    inference(resolution,[],[f90,f42])).
% 1.44/0.54  fof(f106,plain,(
% 1.44/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 1.44/0.54    inference(avatar_component_clause,[],[f104])).
% 1.44/0.54  fof(f104,plain,(
% 1.44/0.54    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.44/0.54  fof(f845,plain,(
% 1.44/0.54    spl1_1 | ~spl1_18),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f844])).
% 1.44/0.54  fof(f844,plain,(
% 1.44/0.54    $false | (spl1_1 | ~spl1_18)),
% 1.44/0.54    inference(subsumption_resolution,[],[f843,f102])).
% 1.44/0.54  fof(f102,plain,(
% 1.44/0.54    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 1.44/0.54    inference(avatar_component_clause,[],[f100])).
% 1.44/0.54  fof(f100,plain,(
% 1.44/0.54    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.44/0.54  fof(f843,plain,(
% 1.44/0.54    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl1_18),
% 1.44/0.54    inference(forward_demodulation,[],[f842,f72])).
% 1.44/0.54  fof(f842,plain,(
% 1.44/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | ~spl1_18),
% 1.44/0.54    inference(forward_demodulation,[],[f841,f86])).
% 1.44/0.54  fof(f841,plain,(
% 1.44/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~spl1_18),
% 1.44/0.54    inference(forward_demodulation,[],[f767,f621])).
% 1.44/0.54  fof(f621,plain,(
% 1.44/0.54    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.44/0.54    inference(resolution,[],[f606,f42])).
% 1.44/0.54  fof(f767,plain,(
% 1.44/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~spl1_18),
% 1.44/0.54    inference(resolution,[],[f73,f444])).
% 1.44/0.54  fof(f444,plain,(
% 1.44/0.54    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_18),
% 1.44/0.54    inference(backward_demodulation,[],[f375,f431])).
% 1.44/0.54  fof(f375,plain,(
% 1.44/0.54    v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | ~spl1_18),
% 1.44/0.54    inference(avatar_component_clause,[],[f374])).
% 1.44/0.54  fof(f374,plain,(
% 1.44/0.54    spl1_18 <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 1.44/0.54  fof(f385,plain,(
% 1.44/0.54    ~spl1_12 | spl1_18),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f384])).
% 1.44/0.54  fof(f384,plain,(
% 1.44/0.54    $false | (~spl1_12 | spl1_18)),
% 1.44/0.54    inference(subsumption_resolution,[],[f383,f287])).
% 1.44/0.54  fof(f287,plain,(
% 1.44/0.54    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_12),
% 1.44/0.54    inference(avatar_component_clause,[],[f286])).
% 1.44/0.54  fof(f286,plain,(
% 1.44/0.54    spl1_12 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.44/0.54  fof(f383,plain,(
% 1.44/0.54    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_18),
% 1.44/0.54    inference(subsumption_resolution,[],[f382,f42])).
% 1.44/0.54  fof(f382,plain,(
% 1.44/0.54    ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_18),
% 1.44/0.54    inference(resolution,[],[f376,f64])).
% 1.44/0.54  fof(f376,plain,(
% 1.44/0.54    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | spl1_18),
% 1.44/0.54    inference(avatar_component_clause,[],[f374])).
% 1.44/0.54  fof(f318,plain,(
% 1.44/0.54    spl1_12),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f317])).
% 1.44/0.54  fof(f317,plain,(
% 1.44/0.54    $false | spl1_12),
% 1.44/0.54    inference(subsumption_resolution,[],[f316,f76])).
% 1.44/0.54  fof(f316,plain,(
% 1.44/0.54    ~v1_relat_1(k1_xboole_0) | spl1_12),
% 1.44/0.54    inference(resolution,[],[f288,f52])).
% 1.44/0.54  fof(f52,plain,(
% 1.44/0.54    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f30])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f16])).
% 1.44/0.54  fof(f16,axiom,(
% 1.44/0.54    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.44/0.54  fof(f288,plain,(
% 1.44/0.54    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_12),
% 1.44/0.54    inference(avatar_component_clause,[],[f286])).
% 1.44/0.54  fof(f296,plain,(
% 1.44/0.54    spl1_11),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f295])).
% 1.44/0.54  fof(f295,plain,(
% 1.44/0.54    $false | spl1_11),
% 1.44/0.54    inference(subsumption_resolution,[],[f294,f42])).
% 1.44/0.54  fof(f294,plain,(
% 1.44/0.54    ~v1_relat_1(sK0) | spl1_11),
% 1.44/0.54    inference(resolution,[],[f284,f52])).
% 1.44/0.54  fof(f284,plain,(
% 1.44/0.54    ~v1_relat_1(k4_relat_1(sK0)) | spl1_11),
% 1.44/0.54    inference(avatar_component_clause,[],[f282])).
% 1.44/0.54  fof(f189,plain,(
% 1.44/0.54    spl1_7),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f188])).
% 1.44/0.54  fof(f188,plain,(
% 1.44/0.54    $false | spl1_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f187,f42])).
% 1.44/0.54  fof(f187,plain,(
% 1.44/0.54    ~v1_relat_1(sK0) | spl1_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f186,f76])).
% 1.44/0.54  fof(f186,plain,(
% 1.44/0.54    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_7),
% 1.44/0.54    inference(resolution,[],[f185,f64])).
% 1.44/0.54  fof(f185,plain,(
% 1.44/0.54    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_7),
% 1.44/0.54    inference(resolution,[],[f179,f52])).
% 1.44/0.54  fof(f179,plain,(
% 1.44/0.54    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f177])).
% 1.44/0.54  fof(f107,plain,(
% 1.44/0.54    ~spl1_1 | ~spl1_2),
% 1.44/0.54    inference(avatar_split_clause,[],[f43,f104,f100])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.44/0.54    inference(cnf_transformation,[],[f41])).
% 1.44/0.54  % SZS output end Proof for theBenchmark
% 1.44/0.54  % (8707)------------------------------
% 1.44/0.54  % (8707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (8707)Termination reason: Refutation
% 1.44/0.54  
% 1.44/0.54  % (8707)Memory used [KB]: 11385
% 1.44/0.54  % (8707)Time elapsed: 0.102 s
% 1.44/0.54  % (8707)------------------------------
% 1.44/0.54  % (8707)------------------------------
% 1.44/0.54  % (8697)Success in time 0.186 s
%------------------------------------------------------------------------------
