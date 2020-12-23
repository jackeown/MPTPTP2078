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
% DateTime   : Thu Dec  3 12:54:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 235 expanded)
%              Number of leaves         :   15 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  225 ( 843 expanded)
%              Number of equality atoms :   52 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f899,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f671,f678,f874])).

fof(f874,plain,(
    ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f850,f32])).

fof(f32,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f850,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f98,f840])).

fof(f840,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f839,f670])).

fof(f670,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f668])).

fof(f668,plain,
    ( spl3_12
  <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f839,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f838,f99])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f838,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f837,f670])).

fof(f837,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f836,f31])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f836,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f835,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f835,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_relat_1(sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f825,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f825,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(superposition,[],[f140,f572])).

fof(f572,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f545,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

% (3856)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f545,plain,(
    k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f233,f58])).

fof(f58,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f233,plain,(
    ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(subsumption_resolution,[],[f232,f27])).

fof(f232,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f231,f28])).

fof(f231,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f193,f31])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f192,f50])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(X0,k9_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
      | ~ v2_funct_1(X0) ) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(backward_demodulation,[],[f92,f50])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f37,f37])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f678,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f676,f27])).

fof(f676,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f675,f28])).

fof(f675,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f674,f31])).

fof(f674,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f666,f40])).

fof(f666,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f664])).

fof(f664,plain,
    ( spl3_11
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f671,plain,
    ( ~ spl3_11
    | spl3_12 ),
    inference(avatar_split_clause,[],[f661,f668,f664])).

fof(f661,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f645,f43])).

fof(f645,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(trivial_inequality_removal,[],[f633])).

fof(f633,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f44,f621])).

fof(f621,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f619,f27])).

fof(f619,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f120,f30])).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | k1_xboole_0 = k4_xboole_0(X2,k10_relat_1(X3,k9_relat_1(X3,X2))) ) ),
    inference(resolution,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:03:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (3851)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (3857)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (3848)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (3847)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3865)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (3841)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3845)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3839)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (3842)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (3866)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3844)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (3840)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (3863)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3862)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (3850)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (3854)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (3843)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (3858)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (3855)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (3855)Refutation not found, incomplete strategy% (3855)------------------------------
% 0.21/0.55  % (3855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3855)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3855)Memory used [KB]: 10618
% 0.21/0.55  % (3855)Time elapsed: 0.139 s
% 0.21/0.55  % (3855)------------------------------
% 0.21/0.55  % (3855)------------------------------
% 0.21/0.55  % (3867)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (3859)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (3867)Refutation not found, incomplete strategy% (3867)------------------------------
% 0.21/0.55  % (3867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3860)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (3852)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (3849)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (3853)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (3861)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (3849)Refutation not found, incomplete strategy% (3849)------------------------------
% 0.21/0.56  % (3849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3868)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (3868)Refutation not found, incomplete strategy% (3868)------------------------------
% 0.21/0.56  % (3868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3868)Memory used [KB]: 1663
% 0.21/0.56  % (3868)Time elapsed: 0.002 s
% 0.21/0.56  % (3868)------------------------------
% 0.21/0.56  % (3868)------------------------------
% 0.21/0.56  % (3849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3849)Memory used [KB]: 10746
% 0.21/0.56  % (3849)Time elapsed: 0.151 s
% 0.21/0.56  % (3849)------------------------------
% 0.21/0.56  % (3849)------------------------------
% 0.21/0.57  % (3867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3867)Memory used [KB]: 10746
% 0.21/0.57  % (3867)Time elapsed: 0.140 s
% 0.21/0.57  % (3867)------------------------------
% 0.21/0.57  % (3867)------------------------------
% 0.21/0.57  % (3845)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f899,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f671,f678,f874])).
% 0.21/0.57  fof(f874,plain,(
% 0.21/0.57    ~spl3_12),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f873])).
% 0.21/0.57  fof(f873,plain,(
% 0.21/0.57    $false | ~spl3_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f850,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.57  fof(f850,plain,(
% 0.21/0.57    r1_tarski(sK0,sK1) | ~spl3_12),
% 0.21/0.57    inference(superposition,[],[f98,f840])).
% 0.21/0.57  fof(f840,plain,(
% 0.21/0.57    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_12),
% 0.21/0.57    inference(forward_demodulation,[],[f839,f670])).
% 0.21/0.57  fof(f670,plain,(
% 0.21/0.57    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f668])).
% 0.21/0.57  fof(f668,plain,(
% 0.21/0.57    spl3_12 <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.57  fof(f839,plain,(
% 0.21/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f838,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f48,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f38,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f47])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.57  fof(f838,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_12),
% 0.21/0.57    inference(forward_demodulation,[],[f837,f670])).
% 0.21/0.57  fof(f837,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f836,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    v2_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f836,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f835,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f835,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_relat_1(sK2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f825,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f825,plain,(
% 0.21/0.57    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 0.21/0.57    inference(superposition,[],[f140,f572])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.57    inference(forward_demodulation,[],[f545,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  % (3856)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  fof(f545,plain,(
% 0.21/0.57    k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.57    inference(superposition,[],[f233,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.57    inference(resolution,[],[f45,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.57  fof(f233,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f232,f27])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(sK2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f231,f28])).
% 0.21/0.57  fof(f231,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.57    inference(resolution,[],[f193,f31])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f192,f50])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f51,f50])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f46,f47,f47])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k10_relat_1(X0,k9_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1 | ~v2_funct_1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f40,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f92,f50])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 0.21/0.57    inference(superposition,[],[f48,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f35,f37,f37])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.57  fof(f678,plain,(
% 0.21/0.57    spl3_11),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f677])).
% 0.21/0.57  fof(f677,plain,(
% 0.21/0.57    $false | spl3_11),
% 0.21/0.57    inference(subsumption_resolution,[],[f676,f27])).
% 0.21/0.57  fof(f676,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl3_11),
% 0.21/0.57    inference(subsumption_resolution,[],[f675,f28])).
% 0.21/0.57  fof(f675,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_11),
% 0.21/0.57    inference(subsumption_resolution,[],[f674,f31])).
% 0.21/0.57  fof(f674,plain,(
% 0.21/0.57    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_11),
% 0.21/0.57    inference(resolution,[],[f666,f40])).
% 0.21/0.57  fof(f666,plain,(
% 0.21/0.57    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) | spl3_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f664])).
% 0.21/0.57  fof(f664,plain,(
% 0.21/0.57    spl3_11 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.57  fof(f671,plain,(
% 0.21/0.57    ~spl3_11 | spl3_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f661,f668,f664])).
% 0.21/0.57  fof(f661,plain,(
% 0.21/0.57    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 0.21/0.57    inference(resolution,[],[f645,f43])).
% 0.21/0.57  fof(f645,plain,(
% 0.21/0.57    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f633])).
% 0.21/0.57  fof(f633,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.57    inference(superposition,[],[f44,f621])).
% 0.21/0.57  fof(f621,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f619,f27])).
% 0.21/0.57  fof(f619,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.57    inference(resolution,[],[f120,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(X3)) | ~v1_relat_1(X3) | k1_xboole_0 = k4_xboole_0(X2,k10_relat_1(X3,k9_relat_1(X3,X2)))) )),
% 0.21/0.57    inference(resolution,[],[f39,f45])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (3845)------------------------------
% 0.21/0.57  % (3845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3845)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (3845)Memory used [KB]: 11129
% 0.21/0.57  % (3845)Time elapsed: 0.160 s
% 0.21/0.57  % (3845)------------------------------
% 0.21/0.57  % (3845)------------------------------
% 0.21/0.57  % (3838)Success in time 0.21 s
%------------------------------------------------------------------------------
