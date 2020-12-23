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
% DateTime   : Thu Dec  3 12:53:52 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 292 expanded)
%              Number of leaves         :   23 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  207 ( 623 expanded)
%              Number of equality atoms :   90 ( 188 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f328,f809])).

fof(f809,plain,(
    ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f807,f45])).

fof(f45,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f807,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f806,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f806,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_9 ),
    inference(superposition,[],[f343,f805])).

fof(f805,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f802,f299])).

fof(f299,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f297,f164])).

fof(f164,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f162,f103])).

fof(f103,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f162,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f157,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f297,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f293,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f293,plain,(
    k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f273,f261])).

fof(f261,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f244,f44])).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f143,f104])).

fof(f104,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f58,f47])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f142,f47])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f60,f50])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f273,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f270,f104])).

fof(f270,plain,(
    ! [X2,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f160,f47])).

fof(f160,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2) ) ),
    inference(forward_demodulation,[],[f158,f49])).

fof(f158,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f52,f47])).

fof(f802,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(superposition,[],[f335,f789])).

fof(f789,plain,
    ( k7_relat_1(sK1,sK0) = k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(k9_relat_1(sK1,sK0)))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f333,f339])).

fof(f339,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f338,f277])).

fof(f277,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f174,f43])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f338,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f329,f299])).

fof(f329,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(resolution,[],[f320,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f320,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl2_9
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f333,plain,
    ( k7_relat_1(sK1,sK0) = k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(k2_relat_1(k7_relat_1(sK1,sK0))))
    | ~ spl2_9 ),
    inference(resolution,[],[f320,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(resolution,[],[f60,f83])).

fof(f335,plain,
    ( ! [X4] : k1_relat_1(k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(X4))) = k10_relat_1(k7_relat_1(sK1,sK0),X4)
    | ~ spl2_9 ),
    inference(resolution,[],[f320,f160])).

fof(f343,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1))
      | r1_tarski(X0,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f81,f225])).

fof(f225,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f82,f43])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f328,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f326,f43])).

fof(f326,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_9 ),
    inference(resolution,[],[f321,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f321,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (15536)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (15552)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (15544)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (15540)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15535)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (15557)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (15549)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (15534)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (15538)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (15539)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (15558)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (15550)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (15541)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (15559)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (15548)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (15563)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (15556)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (15554)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (15560)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (15555)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (15545)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (15562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (15542)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (15546)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (15547)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.57  % (15561)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (15543)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.58  % (15551)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.59  % (15537)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.48/0.59  % (15540)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.59  % SZS output start Proof for theBenchmark
% 1.48/0.59  fof(f810,plain,(
% 1.48/0.59    $false),
% 1.48/0.59    inference(avatar_sat_refutation,[],[f328,f809])).
% 1.48/0.59  fof(f809,plain,(
% 1.48/0.59    ~spl2_9),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f808])).
% 1.48/0.59  fof(f808,plain,(
% 1.48/0.59    $false | ~spl2_9),
% 1.48/0.59    inference(subsumption_resolution,[],[f807,f45])).
% 1.48/0.59  fof(f45,plain,(
% 1.48/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.48/0.59    inference(cnf_transformation,[],[f39])).
% 1.48/0.59  fof(f39,plain,(
% 1.48/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f38])).
% 1.48/0.59  fof(f38,plain,(
% 1.48/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f26,plain,(
% 1.48/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.48/0.59    inference(flattening,[],[f25])).
% 1.48/0.59  fof(f25,plain,(
% 1.48/0.59    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.48/0.59    inference(ennf_transformation,[],[f24])).
% 1.48/0.59  fof(f24,negated_conjecture,(
% 1.48/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.48/0.59    inference(negated_conjecture,[],[f23])).
% 1.48/0.59  fof(f23,conjecture,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.48/0.59  fof(f807,plain,(
% 1.48/0.59    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_9),
% 1.48/0.59    inference(subsumption_resolution,[],[f806,f46])).
% 1.48/0.59  fof(f46,plain,(
% 1.48/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f5])).
% 1.48/0.59  fof(f5,axiom,(
% 1.48/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.48/0.59  fof(f806,plain,(
% 1.48/0.59    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_9),
% 1.48/0.59    inference(superposition,[],[f343,f805])).
% 1.48/0.59  fof(f805,plain,(
% 1.48/0.59    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(forward_demodulation,[],[f802,f299])).
% 1.48/0.59  fof(f299,plain,(
% 1.48/0.59    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.48/0.59    inference(superposition,[],[f297,f164])).
% 1.48/0.59  fof(f164,plain,(
% 1.48/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.48/0.59    inference(forward_demodulation,[],[f162,f103])).
% 1.48/0.59  fof(f103,plain,(
% 1.48/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 1.48/0.59    inference(resolution,[],[f58,f43])).
% 1.48/0.59  fof(f43,plain,(
% 1.48/0.59    v1_relat_1(sK1)),
% 1.48/0.59    inference(cnf_transformation,[],[f39])).
% 1.48/0.59  fof(f58,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f31])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.48/0.59    inference(ennf_transformation,[],[f20])).
% 1.48/0.59  fof(f20,axiom,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.48/0.59  fof(f162,plain,(
% 1.48/0.59    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 1.48/0.59    inference(resolution,[],[f157,f47])).
% 1.48/0.59  fof(f47,plain,(
% 1.48/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f21])).
% 1.48/0.59  fof(f21,axiom,(
% 1.48/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.48/0.59  fof(f157,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 1.48/0.59    inference(resolution,[],[f52,f43])).
% 1.48/0.59  fof(f52,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f28])).
% 1.48/0.59  fof(f28,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f17])).
% 1.48/0.59  fof(f17,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.48/0.59  fof(f297,plain,(
% 1.48/0.59    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 1.48/0.59    inference(forward_demodulation,[],[f293,f49])).
% 1.48/0.59  fof(f49,plain,(
% 1.48/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f18,axiom,(
% 1.48/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.59  fof(f293,plain,(
% 1.48/0.59    k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k6_relat_1(sK0))),
% 1.48/0.59    inference(superposition,[],[f273,f261])).
% 1.48/0.59  fof(f261,plain,(
% 1.48/0.59    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 1.48/0.59    inference(resolution,[],[f244,f44])).
% 1.48/0.59  fof(f44,plain,(
% 1.48/0.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.48/0.59    inference(cnf_transformation,[],[f39])).
% 1.48/0.59  fof(f244,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f143,f104])).
% 1.48/0.59  fof(f104,plain,(
% 1.48/0.59    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.48/0.59    inference(resolution,[],[f58,f47])).
% 1.48/0.59  fof(f143,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f142,f47])).
% 1.48/0.59  fof(f142,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.48/0.59    inference(superposition,[],[f60,f50])).
% 1.48/0.59  fof(f50,plain,(
% 1.48/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f60,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f34])).
% 1.48/0.59  fof(f34,plain,(
% 1.48/0.59    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.48/0.59    inference(flattening,[],[f33])).
% 1.48/0.59  fof(f33,plain,(
% 1.48/0.59    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.59    inference(ennf_transformation,[],[f19])).
% 1.48/0.59  fof(f19,axiom,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.48/0.59  fof(f273,plain,(
% 1.48/0.59    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.48/0.59    inference(forward_demodulation,[],[f270,f104])).
% 1.48/0.59  fof(f270,plain,(
% 1.48/0.59    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2)) )),
% 1.48/0.59    inference(resolution,[],[f160,f47])).
% 1.48/0.59  fof(f160,plain,(
% 1.48/0.59    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)) )),
% 1.48/0.59    inference(forward_demodulation,[],[f158,f49])).
% 1.48/0.59  fof(f158,plain,(
% 1.48/0.59    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 1.48/0.59    inference(resolution,[],[f52,f47])).
% 1.48/0.59  fof(f802,plain,(
% 1.48/0.59    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(superposition,[],[f335,f789])).
% 1.48/0.59  fof(f789,plain,(
% 1.48/0.59    k7_relat_1(sK1,sK0) = k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(k9_relat_1(sK1,sK0))) | ~spl2_9),
% 1.48/0.59    inference(forward_demodulation,[],[f333,f339])).
% 1.48/0.59  fof(f339,plain,(
% 1.48/0.59    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(forward_demodulation,[],[f338,f277])).
% 1.48/0.59  fof(f277,plain,(
% 1.48/0.59    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.48/0.59    inference(resolution,[],[f174,f43])).
% 1.48/0.59  fof(f174,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1)) )),
% 1.48/0.59    inference(resolution,[],[f53,f83])).
% 1.48/0.59  fof(f83,plain,(
% 1.48/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.59    inference(equality_resolution,[],[f62])).
% 1.48/0.59  fof(f62,plain,(
% 1.48/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.59    inference(cnf_transformation,[],[f41])).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.59    inference(flattening,[],[f40])).
% 1.48/0.59  fof(f40,plain,(
% 1.48/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.59    inference(nnf_transformation,[],[f1])).
% 1.48/0.59  fof(f1,axiom,(
% 1.48/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.59  fof(f53,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f29])).
% 1.48/0.59  fof(f29,plain,(
% 1.48/0.59    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f16])).
% 1.48/0.59  fof(f16,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.48/0.59  fof(f338,plain,(
% 1.48/0.59    k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(forward_demodulation,[],[f329,f299])).
% 1.48/0.59  fof(f329,plain,(
% 1.48/0.59    k9_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(resolution,[],[f320,f51])).
% 1.48/0.59  fof(f51,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f27])).
% 1.48/0.59  fof(f27,plain,(
% 1.48/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f14])).
% 1.48/0.59  fof(f14,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.48/0.59  fof(f320,plain,(
% 1.48/0.59    v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_9),
% 1.48/0.59    inference(avatar_component_clause,[],[f319])).
% 1.48/0.59  fof(f319,plain,(
% 1.48/0.59    spl2_9 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.48/0.59  fof(f333,plain,(
% 1.48/0.59    k7_relat_1(sK1,sK0) = k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(k2_relat_1(k7_relat_1(sK1,sK0)))) | ~spl2_9),
% 1.48/0.59    inference(resolution,[],[f320,f140])).
% 1.48/0.59  fof(f140,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.48/0.59    inference(resolution,[],[f60,f83])).
% 1.48/0.59  fof(f335,plain,(
% 1.48/0.59    ( ! [X4] : (k1_relat_1(k5_relat_1(k7_relat_1(sK1,sK0),k6_relat_1(X4))) = k10_relat_1(k7_relat_1(sK1,sK0),X4)) ) | ~spl2_9),
% 1.48/0.59    inference(resolution,[],[f320,f160])).
% 1.48/0.59  fof(f343,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) | r1_tarski(X0,k10_relat_1(sK1,X1))) )),
% 1.48/0.59    inference(superposition,[],[f81,f225])).
% 1.48/0.59  fof(f225,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 1.48/0.59    inference(resolution,[],[f82,f43])).
% 1.48/0.59  fof(f82,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 1.48/0.59    inference(definition_unfolding,[],[f67,f78])).
% 1.48/0.59  fof(f78,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.59    inference(definition_unfolding,[],[f54,f77])).
% 1.48/0.59  fof(f77,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f55,f76])).
% 1.48/0.59  fof(f76,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f66,f75])).
% 1.48/0.59  fof(f75,plain,(
% 1.48/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f69,f74])).
% 1.48/0.59  fof(f74,plain,(
% 1.48/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f70,f73])).
% 1.48/0.59  fof(f73,plain,(
% 1.48/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f71,f72])).
% 1.48/0.59  fof(f72,plain,(
% 1.48/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f11])).
% 1.48/0.59  fof(f11,axiom,(
% 1.48/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.48/0.59  fof(f71,plain,(
% 1.48/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f10])).
% 1.48/0.59  fof(f10,axiom,(
% 1.48/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.59  fof(f70,plain,(
% 1.48/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f9])).
% 1.48/0.59  fof(f9,axiom,(
% 1.48/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.59  fof(f69,plain,(
% 1.48/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f8])).
% 1.48/0.59  fof(f8,axiom,(
% 1.48/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.59  fof(f66,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,axiom,(
% 1.48/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.59  fof(f55,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f6])).
% 1.48/0.59  fof(f6,axiom,(
% 1.48/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.59  fof(f54,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f12])).
% 1.48/0.59  fof(f12,axiom,(
% 1.48/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.48/0.59  fof(f67,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f35])).
% 1.48/0.59  fof(f35,plain,(
% 1.48/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.48/0.59    inference(ennf_transformation,[],[f22])).
% 1.48/0.59  fof(f22,axiom,(
% 1.48/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.48/0.59  fof(f81,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.48/0.59    inference(definition_unfolding,[],[f64,f79])).
% 1.48/0.59  fof(f79,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.59    inference(definition_unfolding,[],[f56,f78])).
% 1.48/0.59  fof(f56,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f3])).
% 1.48/0.59  fof(f3,axiom,(
% 1.48/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.59  fof(f64,plain,(
% 1.48/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f42])).
% 1.48/0.59  fof(f42,plain,(
% 1.48/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.48/0.59    inference(nnf_transformation,[],[f2])).
% 1.48/0.59  fof(f2,axiom,(
% 1.48/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.48/0.59  fof(f328,plain,(
% 1.48/0.59    spl2_9),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f327])).
% 1.48/0.59  fof(f327,plain,(
% 1.48/0.59    $false | spl2_9),
% 1.48/0.59    inference(subsumption_resolution,[],[f326,f43])).
% 1.48/0.59  fof(f326,plain,(
% 1.48/0.59    ~v1_relat_1(sK1) | spl2_9),
% 1.48/0.59    inference(resolution,[],[f321,f57])).
% 1.48/0.59  fof(f57,plain,(
% 1.48/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f30])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f13])).
% 1.48/0.59  fof(f13,axiom,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.48/0.59  fof(f321,plain,(
% 1.48/0.59    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_9),
% 1.48/0.59    inference(avatar_component_clause,[],[f319])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (15540)------------------------------
% 1.48/0.59  % (15540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (15540)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (15540)Memory used [KB]: 11385
% 1.48/0.59  % (15540)Time elapsed: 0.179 s
% 1.48/0.59  % (15540)------------------------------
% 1.48/0.59  % (15540)------------------------------
% 1.48/0.60  % (15533)Success in time 0.226 s
%------------------------------------------------------------------------------
