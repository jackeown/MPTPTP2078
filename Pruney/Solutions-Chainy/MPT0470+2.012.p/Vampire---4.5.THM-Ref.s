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
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 459 expanded)
%              Number of leaves         :   30 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  291 ( 797 expanded)
%              Number of equality atoms :   98 ( 363 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f144,f152,f210,f256,f727,f729])).

fof(f729,plain,
    ( spl1_2
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | spl1_2
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f86,f219])).

fof(f219,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f218,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f218,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f217,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f217,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f211,f181])).

fof(f181,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f172,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f125,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f122,f88])).

fof(f88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f122,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f211,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | ~ spl1_7 ),
    inference(resolution,[],[f187,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f52,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f187,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl1_7
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f86,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f727,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f726])).

fof(f726,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f725,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f725,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f724,f206])).

fof(f206,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f205,f75])).

fof(f205,plain,
    ( k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f204,f103])).

fof(f204,plain,
    ( k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)))
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f197,f109])).

fof(f109,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f105,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f54,f88])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f197,plain,
    ( k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0)))))
    | ~ spl1_5 ),
    inference(resolution,[],[f76,f136])).

fof(f136,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl1_5
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f724,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f719,f351])).

fof(f351,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f263,f276])).

fof(f276,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f275,f75])).

fof(f275,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f274,f103])).

fof(f274,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_xboole_0)))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f269,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_3 ),
    inference(resolution,[],[f172,f128])).

fof(f128,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl1_3
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f269,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))))
    | ~ spl1_9 ),
    inference(resolution,[],[f247,f76])).

fof(f247,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl1_9
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f263,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f257,f206])).

fof(f257,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f169,f88])).

fof(f169,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k4_relat_1(k5_relat_1(X11,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X11)) ) ),
    inference(resolution,[],[f56,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f719,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f355,f41])).

fof(f355,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f114,f88])).

fof(f114,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4))) ) ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f256,plain,
    ( ~ spl1_3
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl1_3
    | spl1_9 ),
    inference(subsumption_resolution,[],[f254,f128])).

fof(f254,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_9 ),
    inference(subsumption_resolution,[],[f253,f88])).

fof(f253,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_9 ),
    inference(resolution,[],[f248,f60])).

fof(f248,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f210,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl1_7 ),
    inference(subsumption_resolution,[],[f208,f41])).

fof(f208,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(subsumption_resolution,[],[f207,f88])).

fof(f207,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(resolution,[],[f188,f60])).

fof(f188,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f152,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f150,f88])).

fof(f150,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_5 ),
    inference(resolution,[],[f137,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f137,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f144,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f142,f41])).

fof(f142,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f129,f50])).

fof(f129,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f87,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f42,f84,f80])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (24999)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (25011)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (25002)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (25007)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (25026)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (25001)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (25026)Refutation not found, incomplete strategy% (25026)------------------------------
% 0.22/0.54  % (25026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25026)Memory used [KB]: 10618
% 0.22/0.54  % (25026)Time elapsed: 0.114 s
% 0.22/0.54  % (25026)------------------------------
% 0.22/0.54  % (25026)------------------------------
% 0.22/0.54  % (25018)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (25003)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (25017)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (25023)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (25000)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (25020)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (25012)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (25015)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (25006)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (25010)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (25027)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (25027)Refutation not found, incomplete strategy% (25027)------------------------------
% 0.22/0.57  % (25027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (25027)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (25027)Memory used [KB]: 1663
% 0.22/0.57  % (25027)Time elapsed: 0.138 s
% 0.22/0.57  % (25027)------------------------------
% 0.22/0.57  % (25027)------------------------------
% 0.22/0.57  % (25025)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (25009)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (25008)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (25019)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (25024)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (25014)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (25014)Refutation not found, incomplete strategy% (25014)------------------------------
% 0.22/0.57  % (25014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (25014)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (25014)Memory used [KB]: 10618
% 0.22/0.57  % (25014)Time elapsed: 0.156 s
% 0.22/0.57  % (25014)------------------------------
% 0.22/0.57  % (25014)------------------------------
% 0.22/0.57  % (25013)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (25016)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (24998)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.58  % (25004)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (25021)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (25008)Refutation not found, incomplete strategy% (25008)------------------------------
% 0.22/0.59  % (25008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (25008)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (25008)Memory used [KB]: 10618
% 0.22/0.59  % (25008)Time elapsed: 0.161 s
% 0.22/0.59  % (25008)------------------------------
% 0.22/0.59  % (25008)------------------------------
% 0.22/0.59  % (25022)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.60  % (25005)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.61  % (25004)Refutation found. Thanks to Tanya!
% 0.22/0.61  % SZS status Theorem for theBenchmark
% 0.22/0.62  % SZS output start Proof for theBenchmark
% 0.22/0.62  fof(f730,plain,(
% 0.22/0.62    $false),
% 0.22/0.62    inference(avatar_sat_refutation,[],[f87,f144,f152,f210,f256,f727,f729])).
% 0.22/0.62  fof(f729,plain,(
% 0.22/0.62    spl1_2 | ~spl1_7),
% 0.22/0.62    inference(avatar_contradiction_clause,[],[f728])).
% 0.22/0.62  fof(f728,plain,(
% 0.22/0.62    $false | (spl1_2 | ~spl1_7)),
% 0.22/0.62    inference(subsumption_resolution,[],[f86,f219])).
% 0.22/0.62  fof(f219,plain,(
% 0.22/0.62    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_7),
% 0.22/0.62    inference(forward_demodulation,[],[f218,f75])).
% 0.22/0.62  fof(f75,plain,(
% 0.22/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.22/0.62    inference(definition_unfolding,[],[f47,f74])).
% 0.22/0.62  fof(f74,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.62    inference(definition_unfolding,[],[f57,f73])).
% 0.22/0.62  fof(f73,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.62    inference(definition_unfolding,[],[f58,f72])).
% 0.22/0.62  fof(f72,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.62    inference(definition_unfolding,[],[f64,f71])).
% 0.22/0.62  fof(f71,plain,(
% 0.22/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.62    inference(definition_unfolding,[],[f65,f70])).
% 0.22/0.62  fof(f70,plain,(
% 0.22/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.62    inference(definition_unfolding,[],[f66,f69])).
% 0.22/0.62  fof(f69,plain,(
% 0.22/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.62    inference(definition_unfolding,[],[f67,f68])).
% 0.22/0.62  fof(f68,plain,(
% 0.22/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f11])).
% 0.22/0.62  fof(f11,axiom,(
% 0.22/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.62  fof(f67,plain,(
% 0.22/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f10])).
% 0.22/0.62  fof(f10,axiom,(
% 0.22/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.62  fof(f66,plain,(
% 0.22/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f9])).
% 0.22/0.62  fof(f9,axiom,(
% 0.22/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.62  fof(f65,plain,(
% 0.22/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f8])).
% 0.22/0.62  fof(f8,axiom,(
% 0.22/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.62  fof(f64,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f7])).
% 0.22/0.62  fof(f7,axiom,(
% 0.22/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.62  fof(f58,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f6])).
% 0.22/0.62  fof(f6,axiom,(
% 0.22/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.62  fof(f57,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f13])).
% 0.22/0.62  fof(f13,axiom,(
% 0.22/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.62  fof(f47,plain,(
% 0.22/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f4])).
% 0.22/0.62  fof(f4,axiom,(
% 0.22/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.62  fof(f218,plain,(
% 0.22/0.62    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | ~spl1_7),
% 0.22/0.62    inference(forward_demodulation,[],[f217,f103])).
% 0.22/0.62  fof(f103,plain,(
% 0.22/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.62    inference(resolution,[],[f90,f43])).
% 0.22/0.62  fof(f43,plain,(
% 0.22/0.62    v1_xboole_0(k1_xboole_0)),
% 0.22/0.62    inference(cnf_transformation,[],[f1])).
% 0.22/0.62  fof(f1,axiom,(
% 0.22/0.62    v1_xboole_0(k1_xboole_0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.62  fof(f90,plain,(
% 0.22/0.62    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.22/0.62    inference(resolution,[],[f59,f49])).
% 0.22/0.62  fof(f49,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.62    inference(cnf_transformation,[],[f27])).
% 0.22/0.62  fof(f27,plain,(
% 0.22/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f2])).
% 0.22/0.62  fof(f2,axiom,(
% 0.22/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.62  fof(f59,plain,(
% 0.22/0.62    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f34])).
% 0.22/0.62  fof(f34,plain,(
% 0.22/0.62    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.62    inference(ennf_transformation,[],[f12])).
% 0.22/0.62  fof(f12,axiom,(
% 0.22/0.62    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.62  fof(f217,plain,(
% 0.22/0.62    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | ~spl1_7),
% 0.22/0.62    inference(forward_demodulation,[],[f211,f181])).
% 0.22/0.62  fof(f181,plain,(
% 0.22/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.62    inference(resolution,[],[f172,f41])).
% 0.22/0.62  fof(f41,plain,(
% 0.22/0.62    v1_relat_1(sK0)),
% 0.22/0.62    inference(cnf_transformation,[],[f38])).
% 0.22/0.62  fof(f38,plain,(
% 0.22/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).
% 0.22/0.62  fof(f37,plain,(
% 0.22/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f25,plain,(
% 0.22/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f24])).
% 0.22/0.62  fof(f24,negated_conjecture,(
% 0.22/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.62    inference(negated_conjecture,[],[f23])).
% 0.22/0.62  fof(f23,conjecture,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.62  fof(f172,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.22/0.62    inference(resolution,[],[f125,f117])).
% 0.22/0.62  fof(f117,plain,(
% 0.22/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.62    inference(resolution,[],[f63,f46])).
% 0.22/0.62  fof(f46,plain,(
% 0.22/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f5])).
% 0.22/0.62  fof(f5,axiom,(
% 0.22/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.62  fof(f63,plain,(
% 0.22/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f40])).
% 0.22/0.62  fof(f40,plain,(
% 0.22/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.62    inference(flattening,[],[f39])).
% 0.22/0.62  fof(f39,plain,(
% 0.22/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.62    inference(nnf_transformation,[],[f3])).
% 0.22/0.62  fof(f3,axiom,(
% 0.22/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.62  fof(f125,plain,(
% 0.22/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f122,f88])).
% 0.22/0.62  fof(f88,plain,(
% 0.22/0.62    v1_relat_1(k1_xboole_0)),
% 0.22/0.62    inference(resolution,[],[f48,f43])).
% 0.22/0.62  fof(f48,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f26])).
% 0.22/0.62  fof(f26,plain,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f14])).
% 0.22/0.62  fof(f14,axiom,(
% 0.22/0.62    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.62  fof(f122,plain,(
% 0.22/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(superposition,[],[f55,f45])).
% 0.22/0.62  fof(f45,plain,(
% 0.22/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.62    inference(cnf_transformation,[],[f22])).
% 0.22/0.62  fof(f22,axiom,(
% 0.22/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.62  fof(f55,plain,(
% 0.22/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f32])).
% 0.22/0.62  fof(f32,plain,(
% 0.22/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f20])).
% 0.22/0.62  fof(f20,axiom,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.62  fof(f211,plain,(
% 0.22/0.62    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) | ~spl1_7),
% 0.22/0.62    inference(resolution,[],[f187,f76])).
% 0.22/0.62  fof(f76,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 0.22/0.62    inference(definition_unfolding,[],[f52,f74])).
% 0.22/0.62  fof(f52,plain,(
% 0.22/0.62    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f30])).
% 0.22/0.62  fof(f30,plain,(
% 0.22/0.62    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f18])).
% 0.22/0.62  fof(f18,axiom,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.22/0.62  fof(f187,plain,(
% 0.22/0.62    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_7),
% 0.22/0.62    inference(avatar_component_clause,[],[f186])).
% 0.22/0.62  fof(f186,plain,(
% 0.22/0.62    spl1_7 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.62  fof(f86,plain,(
% 0.22/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 0.22/0.62    inference(avatar_component_clause,[],[f84])).
% 0.22/0.62  fof(f84,plain,(
% 0.22/0.62    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.62  fof(f727,plain,(
% 0.22/0.62    spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_9),
% 0.22/0.62    inference(avatar_contradiction_clause,[],[f726])).
% 0.22/0.62  fof(f726,plain,(
% 0.22/0.62    $false | (spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_9)),
% 0.22/0.62    inference(subsumption_resolution,[],[f725,f82])).
% 0.22/0.62  fof(f82,plain,(
% 0.22/0.62    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.62    inference(avatar_component_clause,[],[f80])).
% 0.22/0.62  fof(f80,plain,(
% 0.22/0.62    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.62  fof(f725,plain,(
% 0.22/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_3 | ~spl1_5 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f724,f206])).
% 0.22/0.62  fof(f206,plain,(
% 0.22/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.62    inference(forward_demodulation,[],[f205,f75])).
% 0.22/0.62  fof(f205,plain,(
% 0.22/0.62    k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl1_5),
% 0.22/0.62    inference(forward_demodulation,[],[f204,f103])).
% 0.22/0.62  fof(f204,plain,(
% 0.22/0.62    k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))) | ~spl1_5),
% 0.22/0.62    inference(forward_demodulation,[],[f197,f109])).
% 0.22/0.62  fof(f109,plain,(
% 0.22/0.62    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.62    inference(forward_demodulation,[],[f105,f44])).
% 0.22/0.62  fof(f44,plain,(
% 0.22/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.62    inference(cnf_transformation,[],[f22])).
% 0.22/0.62  fof(f105,plain,(
% 0.22/0.62    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.62    inference(resolution,[],[f54,f88])).
% 0.22/0.62  fof(f54,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.62    inference(cnf_transformation,[],[f31])).
% 0.22/0.62  fof(f31,plain,(
% 0.22/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f19])).
% 0.22/0.62  fof(f19,axiom,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.62  fof(f197,plain,(
% 0.22/0.62    k4_relat_1(k1_xboole_0) = k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))) | ~spl1_5),
% 0.22/0.62    inference(resolution,[],[f76,f136])).
% 0.22/0.62  fof(f136,plain,(
% 0.22/0.62    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_5),
% 0.22/0.62    inference(avatar_component_clause,[],[f135])).
% 0.22/0.62  fof(f135,plain,(
% 0.22/0.62    spl1_5 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.62  fof(f724,plain,(
% 0.22/0.62    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_5 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f719,f351])).
% 0.22/0.62  fof(f351,plain,(
% 0.22/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_3 | ~spl1_5 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f263,f276])).
% 0.22/0.62  fof(f276,plain,(
% 0.22/0.62    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | (~spl1_3 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f275,f75])).
% 0.22/0.62  fof(f275,plain,(
% 0.22/0.62    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k1_xboole_0)) | (~spl1_3 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f274,f103])).
% 0.22/0.62  fof(f274,plain,(
% 0.22/0.62    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_xboole_0))) | (~spl1_3 | ~spl1_9)),
% 0.22/0.62    inference(forward_demodulation,[],[f269,f178])).
% 0.22/0.62  fof(f178,plain,(
% 0.22/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_3),
% 0.22/0.62    inference(resolution,[],[f172,f128])).
% 0.22/0.62  fof(f128,plain,(
% 0.22/0.62    v1_relat_1(k4_relat_1(sK0)) | ~spl1_3),
% 0.22/0.62    inference(avatar_component_clause,[],[f127])).
% 0.22/0.62  fof(f127,plain,(
% 0.22/0.62    spl1_3 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.62  fof(f269,plain,(
% 0.22/0.62    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))))) | ~spl1_9),
% 0.22/0.62    inference(resolution,[],[f247,f76])).
% 0.22/0.62  fof(f247,plain,(
% 0.22/0.62    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_9),
% 0.22/0.62    inference(avatar_component_clause,[],[f246])).
% 0.22/0.62  fof(f246,plain,(
% 0.22/0.62    spl1_9 <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.62  fof(f263,plain,(
% 0.22/0.62    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_5),
% 0.22/0.62    inference(forward_demodulation,[],[f257,f206])).
% 0.22/0.63  fof(f257,plain,(
% 0.22/0.63    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 0.22/0.63    inference(resolution,[],[f169,f88])).
% 0.22/0.63  fof(f169,plain,(
% 0.22/0.63    ( ! [X11] : (~v1_relat_1(X11) | k4_relat_1(k5_relat_1(X11,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X11))) )),
% 0.22/0.63    inference(resolution,[],[f56,f41])).
% 0.22/0.63  fof(f56,plain,(
% 0.22/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f33])).
% 0.22/0.63  fof(f33,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.63    inference(ennf_transformation,[],[f21])).
% 0.22/0.63  fof(f21,axiom,(
% 0.22/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.63  fof(f719,plain,(
% 0.22/0.63    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.22/0.63    inference(resolution,[],[f355,f41])).
% 0.22/0.63  fof(f355,plain,(
% 0.22/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0)))) )),
% 0.22/0.63    inference(resolution,[],[f114,f88])).
% 0.22/0.63  fof(f114,plain,(
% 0.22/0.63    ( ! [X4,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X4) | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4)))) )),
% 0.22/0.63    inference(resolution,[],[f60,f51])).
% 0.22/0.63  fof(f51,plain,(
% 0.22/0.63    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.22/0.63    inference(cnf_transformation,[],[f29])).
% 0.22/0.63  fof(f29,plain,(
% 0.22/0.63    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.63    inference(ennf_transformation,[],[f17])).
% 0.22/0.63  fof(f17,axiom,(
% 0.22/0.63    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.63  fof(f60,plain,(
% 0.22/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f36])).
% 0.22/0.63  fof(f36,plain,(
% 0.22/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.63    inference(flattening,[],[f35])).
% 0.22/0.63  fof(f35,plain,(
% 0.22/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f16])).
% 0.22/0.63  fof(f16,axiom,(
% 0.22/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.63  fof(f256,plain,(
% 0.22/0.63    ~spl1_3 | spl1_9),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.63  fof(f255,plain,(
% 0.22/0.63    $false | (~spl1_3 | spl1_9)),
% 0.22/0.63    inference(subsumption_resolution,[],[f254,f128])).
% 0.22/0.63  fof(f254,plain,(
% 0.22/0.63    ~v1_relat_1(k4_relat_1(sK0)) | spl1_9),
% 0.22/0.63    inference(subsumption_resolution,[],[f253,f88])).
% 0.22/0.63  fof(f253,plain,(
% 0.22/0.63    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_9),
% 0.22/0.63    inference(resolution,[],[f248,f60])).
% 0.22/0.63  fof(f248,plain,(
% 0.22/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | spl1_9),
% 0.22/0.63    inference(avatar_component_clause,[],[f246])).
% 0.22/0.63  fof(f210,plain,(
% 0.22/0.63    spl1_7),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f209])).
% 0.22/0.63  fof(f209,plain,(
% 0.22/0.63    $false | spl1_7),
% 0.22/0.63    inference(subsumption_resolution,[],[f208,f41])).
% 0.22/0.63  fof(f208,plain,(
% 0.22/0.63    ~v1_relat_1(sK0) | spl1_7),
% 0.22/0.63    inference(subsumption_resolution,[],[f207,f88])).
% 0.22/0.63  fof(f207,plain,(
% 0.22/0.63    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_7),
% 0.22/0.63    inference(resolution,[],[f188,f60])).
% 0.22/0.63  fof(f188,plain,(
% 0.22/0.63    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_7),
% 0.22/0.63    inference(avatar_component_clause,[],[f186])).
% 0.22/0.63  fof(f152,plain,(
% 0.22/0.63    spl1_5),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.63  fof(f151,plain,(
% 0.22/0.63    $false | spl1_5),
% 0.22/0.63    inference(subsumption_resolution,[],[f150,f88])).
% 0.22/0.63  fof(f150,plain,(
% 0.22/0.63    ~v1_relat_1(k1_xboole_0) | spl1_5),
% 0.22/0.63    inference(resolution,[],[f137,f50])).
% 0.22/0.63  fof(f50,plain,(
% 0.22/0.63    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f28])).
% 0.22/0.63  fof(f28,plain,(
% 0.22/0.63    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.63    inference(ennf_transformation,[],[f15])).
% 0.22/0.63  fof(f15,axiom,(
% 0.22/0.63    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.63  fof(f137,plain,(
% 0.22/0.63    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_5),
% 0.22/0.63    inference(avatar_component_clause,[],[f135])).
% 0.22/0.63  fof(f144,plain,(
% 0.22/0.63    spl1_3),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.63  fof(f143,plain,(
% 0.22/0.63    $false | spl1_3),
% 0.22/0.63    inference(subsumption_resolution,[],[f142,f41])).
% 0.22/0.63  fof(f142,plain,(
% 0.22/0.63    ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.63    inference(resolution,[],[f129,f50])).
% 0.22/0.63  fof(f129,plain,(
% 0.22/0.63    ~v1_relat_1(k4_relat_1(sK0)) | spl1_3),
% 0.22/0.63    inference(avatar_component_clause,[],[f127])).
% 0.22/0.63  fof(f87,plain,(
% 0.22/0.63    ~spl1_1 | ~spl1_2),
% 0.22/0.63    inference(avatar_split_clause,[],[f42,f84,f80])).
% 0.22/0.63  fof(f42,plain,(
% 0.22/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.63    inference(cnf_transformation,[],[f38])).
% 0.22/0.63  % SZS output end Proof for theBenchmark
% 0.22/0.63  % (25004)------------------------------
% 0.22/0.63  % (25004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.63  % (25004)Termination reason: Refutation
% 0.22/0.63  
% 0.22/0.63  % (25004)Memory used [KB]: 11129
% 0.22/0.63  % (25004)Time elapsed: 0.170 s
% 0.22/0.63  % (25004)------------------------------
% 0.22/0.63  % (25004)------------------------------
% 0.22/0.63  % (24997)Success in time 0.267 s
%------------------------------------------------------------------------------
