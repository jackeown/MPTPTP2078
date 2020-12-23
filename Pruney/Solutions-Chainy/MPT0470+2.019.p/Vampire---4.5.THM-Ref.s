%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 366 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  283 ( 761 expanded)
%              Number of equality atoms :  110 ( 373 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f136,f202,f263,f326,f607])).

fof(f607,plain,
    ( spl1_2
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | spl1_2
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f605,f88])).

fof(f88,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f605,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f603,f282])).

fof(f282,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f281,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f56,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f281,plain,(
    k1_xboole_0 = k4_relat_1(k4_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f279,f96])).

fof(f279,plain,(
    k4_relat_1(k4_xboole_0(sK0,sK0)) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) ),
    inference(resolution,[],[f179,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).

fof(f35,plain,
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

fof(f179,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k4_relat_1(k4_xboole_0(X8,sK0)) = k4_xboole_0(k4_relat_1(X8),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k4_xboole_0(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f57,f57])).

fof(f57,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f603,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(backward_demodulation,[],[f486,f601])).

fof(f601,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f594,f337])).

fof(f337,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f336,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
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

fof(f336,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f335,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f335,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f329,f269])).

fof(f269,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_9 ),
    inference(resolution,[],[f250,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f108,f100])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f108,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f49,plain,(
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

fof(f107,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f53,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f250,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl1_9
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f329,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))))
    | ~ spl1_12 ),
    inference(resolution,[],[f315,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f52,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f315,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl1_12
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f594,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f397,f41])).

fof(f397,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f396,f282])).

fof(f396,plain,(
    ! [X0] :
      ( k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f390,f282])).

fof(f390,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f152,f90])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,k4_relat_1(X2))) = k5_relat_1(k4_relat_1(k4_relat_1(X2)),k4_relat_1(X1)) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f486,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f359,f90])).

fof(f359,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(sK0,X7) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X7))) ) ),
    inference(resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f326,plain,
    ( ~ spl1_9
    | spl1_12 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl1_9
    | spl1_12 ),
    inference(subsumption_resolution,[],[f324,f90])).

fof(f324,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_9
    | spl1_12 ),
    inference(subsumption_resolution,[],[f323,f250])).

fof(f323,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_12 ),
    inference(resolution,[],[f316,f60])).

fof(f316,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f314])).

fof(f263,plain,(
    spl1_9 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl1_9 ),
    inference(subsumption_resolution,[],[f261,f41])).

fof(f261,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(resolution,[],[f251,f50])).

fof(f251,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f249])).

fof(f202,plain,
    ( spl1_1
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl1_1
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f200,f84])).

fof(f84,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f200,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f199,f74])).

fof(f199,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f198,f80])).

fof(f198,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f192,f115])).

fof(f115,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f109,f41])).

fof(f192,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl1_3 ),
    inference(resolution,[],[f75,f121])).

fof(f121,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl1_3
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f136,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f134,f90])).

fof(f134,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f133,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f122,f60])).

fof(f122,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f89,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f42,f86,f82])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (13216)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.54  % (13232)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (13219)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.54  % (13224)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.54  % (13219)Refutation not found, incomplete strategy% (13219)------------------------------
% 1.36/0.54  % (13219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (13213)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.54  % (13211)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.54  % (13204)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.54  % (13219)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13219)Memory used [KB]: 10618
% 1.36/0.54  % (13219)Time elapsed: 0.112 s
% 1.36/0.54  % (13219)------------------------------
% 1.36/0.54  % (13219)------------------------------
% 1.36/0.55  % (13213)Refutation not found, incomplete strategy% (13213)------------------------------
% 1.36/0.55  % (13213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (13213)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (13213)Memory used [KB]: 10618
% 1.36/0.55  % (13213)Time elapsed: 0.117 s
% 1.36/0.55  % (13213)------------------------------
% 1.36/0.55  % (13213)------------------------------
% 1.36/0.55  % (13203)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.55  % (13207)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.55  % (13232)Refutation not found, incomplete strategy% (13232)------------------------------
% 1.36/0.55  % (13232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (13232)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (13232)Memory used [KB]: 1663
% 1.36/0.55  % (13232)Time elapsed: 0.126 s
% 1.36/0.55  % (13232)------------------------------
% 1.36/0.55  % (13232)------------------------------
% 1.36/0.55  % (13225)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.56  % (13206)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.52/0.56  % (13231)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.52/0.56  % (13214)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.56  % (13217)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.57  % (13229)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (13208)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.57  % (13221)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.52/0.57  % (13230)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.57  % (13212)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.52/0.58  % (13222)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.52/0.58  % (13223)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.58  % (13231)Refutation not found, incomplete strategy% (13231)------------------------------
% 1.52/0.58  % (13231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (13231)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (13231)Memory used [KB]: 10746
% 1.52/0.58  % (13231)Time elapsed: 0.170 s
% 1.52/0.58  % (13231)------------------------------
% 1.52/0.58  % (13231)------------------------------
% 1.52/0.58  % (13215)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.59  % (13210)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.52/0.59  % (13205)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.59  % (13218)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.59  % (13209)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.59  % (13227)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.60  % (13226)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.61  % (13220)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.62  % (13228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.62  % (13209)Refutation found. Thanks to Tanya!
% 1.52/0.62  % SZS status Theorem for theBenchmark
% 1.52/0.62  % SZS output start Proof for theBenchmark
% 1.52/0.62  fof(f608,plain,(
% 1.52/0.62    $false),
% 1.52/0.62    inference(avatar_sat_refutation,[],[f89,f136,f202,f263,f326,f607])).
% 1.52/0.62  fof(f607,plain,(
% 1.52/0.62    spl1_2 | ~spl1_9 | ~spl1_12),
% 1.52/0.62    inference(avatar_contradiction_clause,[],[f606])).
% 1.52/0.62  fof(f606,plain,(
% 1.52/0.62    $false | (spl1_2 | ~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(subsumption_resolution,[],[f605,f88])).
% 1.52/0.62  fof(f88,plain,(
% 1.52/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 1.52/0.62    inference(avatar_component_clause,[],[f86])).
% 1.52/0.62  fof(f86,plain,(
% 1.52/0.62    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.52/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.52/0.62  fof(f605,plain,(
% 1.52/0.62    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(forward_demodulation,[],[f603,f282])).
% 1.52/0.62  fof(f282,plain,(
% 1.52/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.52/0.62    inference(forward_demodulation,[],[f281,f96])).
% 1.52/0.62  fof(f96,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.52/0.62    inference(superposition,[],[f56,f48])).
% 1.52/0.62  fof(f48,plain,(
% 1.52/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f3])).
% 1.52/0.62  fof(f3,axiom,(
% 1.52/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.52/0.62  fof(f56,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f6])).
% 1.52/0.62  fof(f6,axiom,(
% 1.52/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.52/0.62  fof(f281,plain,(
% 1.52/0.62    k1_xboole_0 = k4_relat_1(k4_xboole_0(sK0,sK0))),
% 1.52/0.62    inference(forward_demodulation,[],[f279,f96])).
% 1.52/0.62  fof(f279,plain,(
% 1.52/0.62    k4_relat_1(k4_xboole_0(sK0,sK0)) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))),
% 1.52/0.62    inference(resolution,[],[f179,f41])).
% 1.52/0.62  fof(f41,plain,(
% 1.52/0.62    v1_relat_1(sK0)),
% 1.52/0.62    inference(cnf_transformation,[],[f36])).
% 1.52/0.62  fof(f36,plain,(
% 1.52/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).
% 1.52/0.62  fof(f35,plain,(
% 1.52/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f25,plain,(
% 1.52/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f24])).
% 1.52/0.62  fof(f24,negated_conjecture,(
% 1.52/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.52/0.62    inference(negated_conjecture,[],[f23])).
% 1.52/0.62  fof(f23,conjecture,(
% 1.52/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.52/0.62  fof(f179,plain,(
% 1.52/0.62    ( ! [X8] : (~v1_relat_1(X8) | k4_relat_1(k4_xboole_0(X8,sK0)) = k4_xboole_0(k4_relat_1(X8),k4_relat_1(sK0))) )),
% 1.52/0.62    inference(resolution,[],[f76,f41])).
% 1.52/0.62  fof(f76,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k4_xboole_0(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f54,f57,f57])).
% 1.52/0.62  fof(f57,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f12])).
% 1.52/0.62  fof(f12,axiom,(
% 1.52/0.62    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.52/0.62  fof(f54,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f31])).
% 1.52/0.62  fof(f31,plain,(
% 1.52/0.62    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f19])).
% 1.52/0.62  fof(f19,axiom,(
% 1.52/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 1.52/0.62  fof(f603,plain,(
% 1.52/0.62    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(backward_demodulation,[],[f486,f601])).
% 1.52/0.62  fof(f601,plain,(
% 1.52/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(forward_demodulation,[],[f594,f337])).
% 1.52/0.62  fof(f337,plain,(
% 1.52/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(forward_demodulation,[],[f336,f74])).
% 1.52/0.62  fof(f74,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f47,f73])).
% 1.52/0.62  fof(f73,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f58,f72])).
% 1.52/0.62  fof(f72,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f59,f71])).
% 1.52/0.62  fof(f71,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f67,f70])).
% 1.52/0.62  fof(f70,plain,(
% 1.52/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f68,f69])).
% 1.52/0.62  fof(f69,plain,(
% 1.52/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f10])).
% 1.52/0.62  fof(f10,axiom,(
% 1.52/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.52/0.62  fof(f68,plain,(
% 1.52/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f9])).
% 1.52/0.62  fof(f9,axiom,(
% 1.52/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.62  fof(f67,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f8])).
% 1.52/0.62  fof(f8,axiom,(
% 1.52/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.62  fof(f59,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f7])).
% 1.52/0.62  fof(f7,axiom,(
% 1.52/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.62  fof(f58,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f13])).
% 1.52/0.62  fof(f13,axiom,(
% 1.52/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.62  fof(f47,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f4])).
% 1.52/0.62  fof(f4,axiom,(
% 1.52/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.52/0.62  fof(f336,plain,(
% 1.52/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0)) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(forward_demodulation,[],[f335,f80])).
% 1.52/0.62  fof(f80,plain,(
% 1.52/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.52/0.62    inference(equality_resolution,[],[f65])).
% 1.52/0.62  fof(f65,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f40])).
% 1.52/0.62  fof(f40,plain,(
% 1.52/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.62    inference(flattening,[],[f39])).
% 1.52/0.62  fof(f39,plain,(
% 1.52/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.62    inference(nnf_transformation,[],[f11])).
% 1.52/0.62  fof(f11,axiom,(
% 1.52/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.52/0.62  fof(f335,plain,(
% 1.52/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))))) | (~spl1_9 | ~spl1_12)),
% 1.52/0.62    inference(forward_demodulation,[],[f329,f269])).
% 1.52/0.62  fof(f269,plain,(
% 1.52/0.62    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_9),
% 1.52/0.62    inference(resolution,[],[f250,f109])).
% 1.52/0.62  fof(f109,plain,(
% 1.52/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.52/0.62    inference(resolution,[],[f108,f100])).
% 1.52/0.62  fof(f100,plain,(
% 1.52/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.52/0.62    inference(resolution,[],[f63,f46])).
% 1.52/0.62  fof(f46,plain,(
% 1.52/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f5])).
% 1.52/0.62  fof(f5,axiom,(
% 1.52/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.52/0.62  fof(f63,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f38])).
% 1.52/0.62  fof(f38,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(flattening,[],[f37])).
% 1.52/0.62  fof(f37,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(nnf_transformation,[],[f2])).
% 1.52/0.62  fof(f2,axiom,(
% 1.52/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.62  fof(f108,plain,(
% 1.52/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f107,f90])).
% 1.52/0.62  fof(f90,plain,(
% 1.52/0.62    v1_relat_1(k1_xboole_0)),
% 1.52/0.62    inference(resolution,[],[f49,f43])).
% 1.52/0.62  fof(f43,plain,(
% 1.52/0.62    v1_xboole_0(k1_xboole_0)),
% 1.52/0.62    inference(cnf_transformation,[],[f1])).
% 1.52/0.62  fof(f1,axiom,(
% 1.52/0.62    v1_xboole_0(k1_xboole_0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.62  fof(f49,plain,(
% 1.52/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f26])).
% 1.52/0.62  fof(f26,plain,(
% 1.52/0.62    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f14])).
% 1.52/0.62  fof(f14,axiom,(
% 1.52/0.62    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.52/0.62  fof(f107,plain,(
% 1.52/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.52/0.62    inference(superposition,[],[f53,f44])).
% 1.52/0.62  fof(f44,plain,(
% 1.52/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.52/0.62    inference(cnf_transformation,[],[f22])).
% 1.52/0.62  fof(f22,axiom,(
% 1.52/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.52/0.62  fof(f53,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f30])).
% 1.52/0.62  fof(f30,plain,(
% 1.52/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f20])).
% 1.52/0.62  fof(f20,axiom,(
% 1.52/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.52/0.62  fof(f250,plain,(
% 1.52/0.62    v1_relat_1(k4_relat_1(sK0)) | ~spl1_9),
% 1.52/0.62    inference(avatar_component_clause,[],[f249])).
% 1.52/0.62  fof(f249,plain,(
% 1.52/0.62    spl1_9 <=> v1_relat_1(k4_relat_1(sK0))),
% 1.52/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 1.52/0.62  fof(f329,plain,(
% 1.52/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))))) | ~spl1_12),
% 1.52/0.62    inference(resolution,[],[f315,f75])).
% 1.52/0.62  fof(f75,plain,(
% 1.52/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.52/0.62    inference(definition_unfolding,[],[f52,f73])).
% 1.52/0.62  fof(f52,plain,(
% 1.52/0.62    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f29])).
% 1.52/0.62  fof(f29,plain,(
% 1.52/0.62    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f18])).
% 1.52/0.62  fof(f18,axiom,(
% 1.52/0.62    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.52/0.62  fof(f315,plain,(
% 1.52/0.62    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_12),
% 1.52/0.62    inference(avatar_component_clause,[],[f314])).
% 1.52/0.62  fof(f314,plain,(
% 1.52/0.62    spl1_12 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.52/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.52/0.62  fof(f594,plain,(
% 1.52/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.52/0.62    inference(resolution,[],[f397,f41])).
% 1.52/0.62  fof(f397,plain,(
% 1.52/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.52/0.62    inference(forward_demodulation,[],[f396,f282])).
% 1.52/0.62  fof(f396,plain,(
% 1.52/0.62    ( ! [X0] : (k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.62    inference(forward_demodulation,[],[f390,f282])).
% 1.52/0.63  fof(f390,plain,(
% 1.52/0.63    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X0))) )),
% 1.52/0.63    inference(resolution,[],[f152,f90])).
% 1.52/0.63  fof(f152,plain,(
% 1.52/0.63    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k4_relat_1(X2))) = k5_relat_1(k4_relat_1(k4_relat_1(X2)),k4_relat_1(X1))) )),
% 1.52/0.63    inference(resolution,[],[f55,f50])).
% 1.52/0.63  fof(f50,plain,(
% 1.52/0.63    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.63    inference(cnf_transformation,[],[f27])).
% 1.52/0.63  fof(f27,plain,(
% 1.52/0.63    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.63    inference(ennf_transformation,[],[f15])).
% 1.52/0.63  fof(f15,axiom,(
% 1.52/0.63    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.52/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.52/0.63  fof(f55,plain,(
% 1.52/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.63    inference(cnf_transformation,[],[f32])).
% 1.52/0.63  fof(f32,plain,(
% 1.52/0.63    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.63    inference(ennf_transformation,[],[f21])).
% 1.52/0.63  fof(f21,axiom,(
% 1.52/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.52/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.52/0.63  fof(f486,plain,(
% 1.52/0.63    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.52/0.63    inference(resolution,[],[f359,f90])).
% 1.52/0.63  fof(f359,plain,(
% 1.52/0.63    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(sK0,X7) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X7)))) )),
% 1.52/0.63    inference(resolution,[],[f97,f41])).
% 1.52/0.63  fof(f97,plain,(
% 1.52/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 1.52/0.63    inference(resolution,[],[f60,f51])).
% 1.52/0.63  fof(f51,plain,(
% 1.52/0.63    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.52/0.63    inference(cnf_transformation,[],[f28])).
% 1.52/0.63  fof(f28,plain,(
% 1.52/0.63    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.52/0.63    inference(ennf_transformation,[],[f17])).
% 1.52/0.63  fof(f17,axiom,(
% 1.52/0.63    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.52/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.52/0.63  fof(f60,plain,(
% 1.52/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.63    inference(cnf_transformation,[],[f34])).
% 1.52/0.63  fof(f34,plain,(
% 1.52/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.52/0.63    inference(flattening,[],[f33])).
% 1.52/0.63  fof(f33,plain,(
% 1.52/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.52/0.63    inference(ennf_transformation,[],[f16])).
% 1.52/0.63  fof(f16,axiom,(
% 1.52/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.52/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.52/0.63  fof(f326,plain,(
% 1.52/0.63    ~spl1_9 | spl1_12),
% 1.52/0.63    inference(avatar_contradiction_clause,[],[f325])).
% 1.52/0.63  fof(f325,plain,(
% 1.52/0.63    $false | (~spl1_9 | spl1_12)),
% 1.52/0.63    inference(subsumption_resolution,[],[f324,f90])).
% 1.52/0.63  fof(f324,plain,(
% 1.52/0.63    ~v1_relat_1(k1_xboole_0) | (~spl1_9 | spl1_12)),
% 1.52/0.63    inference(subsumption_resolution,[],[f323,f250])).
% 1.52/0.63  fof(f323,plain,(
% 1.52/0.63    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_12),
% 1.52/0.63    inference(resolution,[],[f316,f60])).
% 1.52/0.63  fof(f316,plain,(
% 1.52/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl1_12),
% 1.52/0.63    inference(avatar_component_clause,[],[f314])).
% 1.52/0.63  fof(f263,plain,(
% 1.52/0.63    spl1_9),
% 1.52/0.63    inference(avatar_contradiction_clause,[],[f262])).
% 1.52/0.63  fof(f262,plain,(
% 1.52/0.63    $false | spl1_9),
% 1.52/0.63    inference(subsumption_resolution,[],[f261,f41])).
% 1.52/0.63  fof(f261,plain,(
% 1.52/0.63    ~v1_relat_1(sK0) | spl1_9),
% 1.52/0.63    inference(resolution,[],[f251,f50])).
% 1.52/0.63  fof(f251,plain,(
% 1.52/0.63    ~v1_relat_1(k4_relat_1(sK0)) | spl1_9),
% 1.52/0.63    inference(avatar_component_clause,[],[f249])).
% 1.52/0.63  fof(f202,plain,(
% 1.52/0.63    spl1_1 | ~spl1_3),
% 1.52/0.63    inference(avatar_contradiction_clause,[],[f201])).
% 1.52/0.63  fof(f201,plain,(
% 1.52/0.63    $false | (spl1_1 | ~spl1_3)),
% 1.52/0.63    inference(subsumption_resolution,[],[f200,f84])).
% 1.52/0.63  fof(f84,plain,(
% 1.52/0.63    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 1.52/0.63    inference(avatar_component_clause,[],[f82])).
% 1.52/0.63  fof(f82,plain,(
% 1.52/0.63    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.52/0.63    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.96/0.63  fof(f200,plain,(
% 1.96/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl1_3),
% 1.96/0.63    inference(forward_demodulation,[],[f199,f74])).
% 1.96/0.63  fof(f199,plain,(
% 1.96/0.63    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | ~spl1_3),
% 1.96/0.63    inference(forward_demodulation,[],[f198,f80])).
% 1.96/0.63  fof(f198,plain,(
% 1.96/0.63    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~spl1_3),
% 1.96/0.63    inference(forward_demodulation,[],[f192,f115])).
% 1.96/0.63  fof(f115,plain,(
% 1.96/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.96/0.63    inference(resolution,[],[f109,f41])).
% 1.96/0.63  fof(f192,plain,(
% 1.96/0.63    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~spl1_3),
% 1.96/0.63    inference(resolution,[],[f75,f121])).
% 1.96/0.63  fof(f121,plain,(
% 1.96/0.63    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_3),
% 1.96/0.63    inference(avatar_component_clause,[],[f120])).
% 1.96/0.63  fof(f120,plain,(
% 1.96/0.63    spl1_3 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.96/0.63  fof(f136,plain,(
% 1.96/0.63    spl1_3),
% 1.96/0.63    inference(avatar_contradiction_clause,[],[f135])).
% 1.96/0.63  fof(f135,plain,(
% 1.96/0.63    $false | spl1_3),
% 1.96/0.63    inference(subsumption_resolution,[],[f134,f90])).
% 1.96/0.63  fof(f134,plain,(
% 1.96/0.63    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 1.96/0.63    inference(subsumption_resolution,[],[f133,f41])).
% 1.96/0.63  fof(f133,plain,(
% 1.96/0.63    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_3),
% 1.96/0.63    inference(resolution,[],[f122,f60])).
% 1.96/0.63  fof(f122,plain,(
% 1.96/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_3),
% 1.96/0.63    inference(avatar_component_clause,[],[f120])).
% 1.96/0.63  fof(f89,plain,(
% 1.96/0.63    ~spl1_1 | ~spl1_2),
% 1.96/0.63    inference(avatar_split_clause,[],[f42,f86,f82])).
% 1.96/0.63  fof(f42,plain,(
% 1.96/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.96/0.63    inference(cnf_transformation,[],[f36])).
% 1.96/0.63  % SZS output end Proof for theBenchmark
% 1.96/0.63  % (13209)------------------------------
% 1.96/0.63  % (13209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (13209)Termination reason: Refutation
% 1.96/0.63  
% 1.96/0.63  % (13209)Memory used [KB]: 11001
% 1.96/0.63  % (13209)Time elapsed: 0.139 s
% 1.96/0.63  % (13209)------------------------------
% 1.96/0.63  % (13209)------------------------------
% 1.96/0.63  % (13202)Success in time 0.264 s
%------------------------------------------------------------------------------
