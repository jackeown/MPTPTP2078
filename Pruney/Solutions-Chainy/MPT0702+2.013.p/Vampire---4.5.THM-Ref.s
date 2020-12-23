%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 220 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  211 ( 865 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f233,f255,f313])).

fof(f313,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f306,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).

fof(f21,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f306,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f79,f299])).

fof(f299,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f298,f232])).

fof(f232,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl3_6
  <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f298,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f297,f71])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f297,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),sK0)
    | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f296,f232])).

fof(f296,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f295,f29])).

fof(f29,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f295,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f294,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f294,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_relat_1(sK2)
    | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f291,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f291,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(superposition,[],[f100,f159])).

fof(f159,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f117,f70])).

fof(f70,plain,(
    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(subsumption_resolution,[],[f116,f25])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f26])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f40,f32,f32])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k10_relat_1(X2,k9_relat_1(X2,X3)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k9_relat_1(X2,X3)) = X3
      | ~ v2_funct_1(X2) ) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f255,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f253,f25])).

fof(f253,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f252,f26])).

fof(f252,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f251,f29])).

fof(f251,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f228,f35])).

fof(f228,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f233,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f224,f230,f226])).

fof(f224,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f220,f38])).

fof(f220,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f79,f203])).

fof(f203,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) ),
    inference(subsumption_resolution,[],[f199,f25])).

fof(f199,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0 ) ),
    inference(resolution,[],[f33,f42])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.50  % (6192)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (6175)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (6190)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (6176)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6185)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (6174)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (6173)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (6198)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (6198)Refutation not found, incomplete strategy% (6198)------------------------------
% 0.20/0.52  % (6198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6198)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6198)Memory used [KB]: 10746
% 0.20/0.52  % (6198)Time elapsed: 0.122 s
% 0.20/0.52  % (6198)------------------------------
% 0.20/0.52  % (6198)------------------------------
% 0.20/0.52  % (6177)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (6184)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (6179)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (6193)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (6181)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (6176)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (6180)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (6189)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (6172)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (6170)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (6194)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (6197)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (6188)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.54  % (6182)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.54  % (6191)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.54  % (6196)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.54  % (6195)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.54  % SZS output start Proof for theBenchmark
% 1.48/0.54  fof(f314,plain,(
% 1.48/0.54    $false),
% 1.48/0.54    inference(avatar_sat_refutation,[],[f233,f255,f313])).
% 1.48/0.54  fof(f313,plain,(
% 1.48/0.54    ~spl3_6),
% 1.48/0.54    inference(avatar_contradiction_clause,[],[f312])).
% 1.48/0.54  fof(f312,plain,(
% 1.48/0.54    $false | ~spl3_6),
% 1.48/0.54    inference(subsumption_resolution,[],[f306,f30])).
% 1.48/0.54  fof(f30,plain,(
% 1.48/0.54    ~r1_tarski(sK0,sK1)),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f22,plain,(
% 1.48/0.54    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.48/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).
% 1.48/0.54  fof(f21,plain,(
% 1.48/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.48/0.54    introduced(choice_axiom,[])).
% 1.48/0.54  fof(f12,plain,(
% 1.48/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.48/0.54    inference(flattening,[],[f11])).
% 1.48/0.54  fof(f11,plain,(
% 1.48/0.54    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.48/0.54    inference(ennf_transformation,[],[f10])).
% 1.48/0.54  fof(f10,negated_conjecture,(
% 1.48/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.48/0.54    inference(negated_conjecture,[],[f9])).
% 1.48/0.54  fof(f9,conjecture,(
% 1.48/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 1.48/0.54  fof(f306,plain,(
% 1.48/0.54    r1_tarski(sK0,sK1) | ~spl3_6),
% 1.48/0.54    inference(superposition,[],[f79,f299])).
% 1.48/0.54  fof(f299,plain,(
% 1.48/0.54    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_6),
% 1.48/0.54    inference(forward_demodulation,[],[f298,f232])).
% 1.48/0.54  fof(f232,plain,(
% 1.48/0.54    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_6),
% 1.48/0.54    inference(avatar_component_clause,[],[f230])).
% 1.48/0.54  fof(f230,plain,(
% 1.48/0.54    spl3_6 <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.48/0.54  fof(f298,plain,(
% 1.48/0.54    k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_6),
% 1.48/0.54    inference(subsumption_resolution,[],[f297,f71])).
% 1.48/0.54  fof(f71,plain,(
% 1.48/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.48/0.54    inference(resolution,[],[f43,f45])).
% 1.48/0.54  fof(f45,plain,(
% 1.48/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.54    inference(equality_resolution,[],[f37])).
% 1.48/0.54  fof(f37,plain,(
% 1.48/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.54    inference(cnf_transformation,[],[f24])).
% 1.48/0.54  fof(f24,plain,(
% 1.48/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.54    inference(flattening,[],[f23])).
% 1.48/0.54  fof(f23,plain,(
% 1.48/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.54    inference(nnf_transformation,[],[f2])).
% 1.48/0.54  fof(f2,axiom,(
% 1.48/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.54  fof(f43,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 1.48/0.54    inference(definition_unfolding,[],[f39,f32])).
% 1.48/0.54  fof(f32,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f5])).
% 1.48/0.54  fof(f5,axiom,(
% 1.48/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.48/0.54  fof(f39,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f18])).
% 1.48/0.54  fof(f18,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.48/0.54    inference(ennf_transformation,[],[f3])).
% 1.48/0.54  fof(f3,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.48/0.54  fof(f297,plain,(
% 1.48/0.54    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),sK0) | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_6),
% 1.48/0.54    inference(forward_demodulation,[],[f296,f232])).
% 1.48/0.54  fof(f296,plain,(
% 1.48/0.54    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.48/0.54    inference(subsumption_resolution,[],[f295,f29])).
% 1.48/0.54  fof(f29,plain,(
% 1.48/0.54    v2_funct_1(sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f295,plain,(
% 1.48/0.54    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 1.48/0.54    inference(subsumption_resolution,[],[f294,f25])).
% 1.48/0.54  fof(f25,plain,(
% 1.48/0.54    v1_relat_1(sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f294,plain,(
% 1.48/0.54    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_relat_1(sK2) | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 1.48/0.54    inference(subsumption_resolution,[],[f291,f26])).
% 1.48/0.54  fof(f26,plain,(
% 1.48/0.54    v1_funct_1(sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f291,plain,(
% 1.48/0.54    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_setfam_1(k2_tarski(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 1.48/0.54    inference(superposition,[],[f100,f159])).
% 1.48/0.54  fof(f159,plain,(
% 1.48/0.54    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.48/0.54    inference(superposition,[],[f117,f70])).
% 1.48/0.54  fof(f70,plain,(
% 1.48/0.54    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.48/0.54    inference(resolution,[],[f42,f27])).
% 1.48/0.54  fof(f27,plain,(
% 1.48/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f42,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.48/0.54    inference(definition_unfolding,[],[f34,f32])).
% 1.48/0.54  fof(f34,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f15])).
% 1.48/0.54  fof(f15,plain,(
% 1.48/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.54    inference(ennf_transformation,[],[f4])).
% 1.48/0.54  fof(f4,axiom,(
% 1.48/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.54  fof(f117,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f116,f25])).
% 1.48/0.54  fof(f116,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f115,f26])).
% 1.48/0.54  fof(f115,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.54    inference(resolution,[],[f44,f29])).
% 1.48/0.54  fof(f44,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.48/0.54    inference(definition_unfolding,[],[f40,f32,f32])).
% 1.48/0.54  fof(f40,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f20])).
% 1.48/0.54  fof(f20,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.54    inference(flattening,[],[f19])).
% 1.48/0.54  fof(f19,plain,(
% 1.48/0.54    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.48/0.54    inference(ennf_transformation,[],[f6])).
% 1.48/0.54  fof(f6,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 1.48/0.54  fof(f100,plain,(
% 1.48/0.54    ( ! [X2,X3] : (~r1_tarski(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k9_relat_1(X2,X3)) = X3 | ~v2_funct_1(X2)) )),
% 1.48/0.54    inference(resolution,[],[f35,f38])).
% 1.48/0.54  fof(f38,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f24])).
% 1.48/0.54  fof(f35,plain,(
% 1.48/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f17])).
% 1.48/0.54  fof(f17,plain,(
% 1.48/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/0.54    inference(flattening,[],[f16])).
% 1.48/0.54  fof(f16,plain,(
% 1.48/0.54    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.48/0.54    inference(ennf_transformation,[],[f8])).
% 1.48/0.54  fof(f8,axiom,(
% 1.48/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.48/0.54  fof(f79,plain,(
% 1.48/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.48/0.54    inference(superposition,[],[f71,f41])).
% 1.48/0.54  fof(f41,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f31,f32,f32])).
% 1.48/0.54  fof(f31,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f1])).
% 1.48/0.54  fof(f1,axiom,(
% 1.48/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.48/0.54  fof(f255,plain,(
% 1.48/0.54    spl3_5),
% 1.48/0.54    inference(avatar_contradiction_clause,[],[f254])).
% 1.48/0.54  fof(f254,plain,(
% 1.48/0.54    $false | spl3_5),
% 1.48/0.54    inference(subsumption_resolution,[],[f253,f25])).
% 1.48/0.54  fof(f253,plain,(
% 1.48/0.54    ~v1_relat_1(sK2) | spl3_5),
% 1.48/0.54    inference(subsumption_resolution,[],[f252,f26])).
% 1.48/0.54  fof(f252,plain,(
% 1.48/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 1.48/0.54    inference(subsumption_resolution,[],[f251,f29])).
% 1.48/0.54  fof(f251,plain,(
% 1.48/0.54    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 1.48/0.54    inference(resolution,[],[f228,f35])).
% 1.48/0.54  fof(f228,plain,(
% 1.48/0.54    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) | spl3_5),
% 1.48/0.54    inference(avatar_component_clause,[],[f226])).
% 1.48/0.54  fof(f226,plain,(
% 1.48/0.54    spl3_5 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.48/0.54  fof(f233,plain,(
% 1.48/0.54    ~spl3_5 | spl3_6),
% 1.48/0.54    inference(avatar_split_clause,[],[f224,f230,f226])).
% 1.48/0.54  fof(f224,plain,(
% 1.48/0.54    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 1.48/0.54    inference(resolution,[],[f220,f38])).
% 1.48/0.54  fof(f220,plain,(
% 1.48/0.54    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 1.48/0.54    inference(superposition,[],[f79,f203])).
% 1.48/0.54  fof(f203,plain,(
% 1.48/0.54    sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))),
% 1.48/0.54    inference(subsumption_resolution,[],[f199,f25])).
% 1.48/0.54  fof(f199,plain,(
% 1.48/0.54    ~v1_relat_1(sK2) | sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))),
% 1.48/0.54    inference(resolution,[],[f83,f28])).
% 1.48/0.54  fof(f28,plain,(
% 1.48/0.54    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f83,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0) )),
% 1.48/0.54    inference(resolution,[],[f33,f42])).
% 1.48/0.54  fof(f33,plain,(
% 1.48/0.54    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f14])).
% 1.48/0.54  fof(f14,plain,(
% 1.48/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.48/0.54    inference(flattening,[],[f13])).
% 1.48/0.54  fof(f13,plain,(
% 1.48/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.48/0.54    inference(ennf_transformation,[],[f7])).
% 1.48/0.54  fof(f7,axiom,(
% 1.48/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.48/0.54  % SZS output end Proof for theBenchmark
% 1.48/0.54  % (6176)------------------------------
% 1.48/0.54  % (6176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (6176)Termination reason: Refutation
% 1.48/0.54  
% 1.48/0.54  % (6176)Memory used [KB]: 10874
% 1.48/0.54  % (6176)Time elapsed: 0.100 s
% 1.48/0.54  % (6176)------------------------------
% 1.48/0.54  % (6176)------------------------------
% 1.48/0.54  % (6171)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.48/0.54  % (6169)Success in time 0.183 s
%------------------------------------------------------------------------------
