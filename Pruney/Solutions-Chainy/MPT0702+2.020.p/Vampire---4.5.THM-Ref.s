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
% DateTime   : Thu Dec  3 12:54:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 345 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   20
%              Number of atoms          :  349 (1465 expanded)
%              Number of equality atoms :   72 ( 119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f890,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f259,f263,f271,f889])).

fof(f889,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f888])).

fof(f888,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f887,f52])).

fof(f52,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f42])).

fof(f42,plain,
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

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f887,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f885,f182])).

fof(f182,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f179,f159])).

fof(f159,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f64,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f179,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK2)))) ),
    inference(resolution,[],[f80,f50])).

% (23203)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f76])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f885,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f81,f875])).

fof(f875,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(resolution,[],[f867,f107])).

fof(f107,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k1_setfam_1(k1_enumset1(X4,X4,X5)))
      | k1_setfam_1(k1_enumset1(X4,X4,X5)) = X4 ) ),
    inference(resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f867,plain,
    ( r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f866,f432])).

fof(f432,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f427,f237])).

fof(f237,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f236,f47])).

fof(f47,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f236,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f235,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f235,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f66,f51])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f427,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f309,f267])).

fof(f267,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f266,f47])).

fof(f266,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f265,f48])).

fof(f265,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f309,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f308,f242])).

fof(f242,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl3_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f308,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f303,f246])).

fof(f246,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl3_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f303,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(resolution,[],[f286,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f286,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_11 ),
    inference(resolution,[],[f283,f94])).

fof(f94,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK2),X2)
      | r1_tarski(sK0,X2) ) ),
    inference(superposition,[],[f74,f90])).

fof(f90,plain,(
    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f283,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f258,f95])).

fof(f95,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f54,f47])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f258,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl3_11
  <=> ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f866,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(subsumption_resolution,[],[f865,f47])).

fof(f865,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f864,f48])).

fof(f864,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f855,f51])).

fof(f855,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f65,f602])).

fof(f602,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f321,f155])).

fof(f155,plain,(
    k9_relat_1(sK2,sK0) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f321,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(subsumption_resolution,[],[f320,f47])).

fof(f320,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f319,f48])).

fof(f319,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f82,f51])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f75,f76,f76])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f271,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f269,f47])).

fof(f269,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f268,f48])).

fof(f268,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(resolution,[],[f247,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f247,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f245])).

fof(f263,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f261,f47])).

fof(f261,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f260,f48])).

fof(f260,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f243,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f243,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f241])).

fof(f259,plain,
    ( ~ spl3_7
    | spl3_11 ),
    inference(avatar_split_clause,[],[f239,f257,f241])).

fof(f239,plain,(
    ! [X1] :
      ( r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f61,f237])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (23205)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (23217)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (23209)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (23219)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (23201)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (23211)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (23205)Refutation not found, incomplete strategy% (23205)------------------------------
% 0.20/0.52  % (23205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23205)Memory used [KB]: 10746
% 0.20/0.52  % (23205)Time elapsed: 0.102 s
% 0.20/0.52  % (23205)------------------------------
% 0.20/0.52  % (23205)------------------------------
% 0.20/0.52  % (23206)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (23211)Refutation not found, incomplete strategy% (23211)------------------------------
% 0.20/0.52  % (23211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23211)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23211)Memory used [KB]: 10618
% 0.20/0.52  % (23211)Time elapsed: 0.112 s
% 0.20/0.52  % (23211)------------------------------
% 0.20/0.52  % (23211)------------------------------
% 0.20/0.52  % (23199)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (23202)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (23196)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (23204)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (23195)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (23197)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (23198)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (23200)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (23213)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (23223)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (23222)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (23210)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (23224)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (23224)Refutation not found, incomplete strategy% (23224)------------------------------
% 0.20/0.54  % (23224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23224)Memory used [KB]: 1663
% 0.20/0.54  % (23224)Time elapsed: 0.001 s
% 0.20/0.54  % (23224)------------------------------
% 0.20/0.54  % (23224)------------------------------
% 0.20/0.54  % (23215)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (23214)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (23218)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (23216)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (23220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (23207)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (23201)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f890,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f259,f263,f271,f889])).
% 0.20/0.55  fof(f889,plain,(
% 0.20/0.55    ~spl3_7 | ~spl3_8 | ~spl3_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f888])).
% 0.20/0.55  fof(f888,plain,(
% 0.20/0.55    $false | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f887,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f20])).
% 0.20/0.55  fof(f20,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 0.20/0.55  fof(f887,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f885,f182])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.20/0.55    inference(forward_demodulation,[],[f179,f159])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK2)))),
% 0.20/0.55    inference(resolution,[],[f79,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f64,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f58,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK2))))),
% 0.20/0.55    inference(resolution,[],[f80,f50])).
% 0.20/0.55  % (23203)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f73,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f60,f76])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.55  fof(f885,plain,(
% 0.20/0.55    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK1) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(superposition,[],[f81,f875])).
% 0.20/0.55  fof(f875,plain,(
% 0.20/0.55    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(resolution,[],[f867,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X4,X5] : (~r1_tarski(X4,k1_setfam_1(k1_enumset1(X4,X4,X5))) | k1_setfam_1(k1_enumset1(X4,X4,X5)) = X4) )),
% 0.20/0.55    inference(resolution,[],[f71,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f57,f76])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f867,plain,(
% 0.20/0.55    r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(forward_demodulation,[],[f866,f432])).
% 0.20/0.55  fof(f432,plain,(
% 0.20/0.55    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(superposition,[],[f427,f237])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f236,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    v1_relat_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f235,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(resolution,[],[f66,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    v2_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.20/0.55  fof(f427,plain,(
% 0.20/0.55    sK0 = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0)) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(forward_demodulation,[],[f309,f267])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f266,f47])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f265,f48])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(resolution,[],[f67,f51])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.55  fof(f309,plain,(
% 0.20/0.55    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | (~spl3_7 | ~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f308,f242])).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    v1_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f241])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    spl3_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.55  fof(f308,plain,(
% 0.20/0.55    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f303,f246])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    v1_funct_1(k2_funct_1(sK2)) | ~spl3_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f245])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    spl3_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.55  fof(f303,plain,(
% 0.20/0.55    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.20/0.55    inference(resolution,[],[f286,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~spl3_11),
% 0.20/0.55    inference(resolution,[],[f283,f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | r1_tarski(sK0,X2)) )),
% 0.20/0.55    inference(superposition,[],[f74,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2))),
% 0.20/0.55    inference(resolution,[],[f63,f50])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.55  fof(f283,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl3_11),
% 0.20/0.55    inference(superposition,[],[f258,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.20/0.55    inference(resolution,[],[f54,f47])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))) ) | ~spl3_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f257])).
% 0.20/0.55  fof(f257,plain,(
% 0.20/0.55    spl3_11 <=> ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.55  fof(f866,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f865,f47])).
% 0.20/0.55  fof(f865,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f864,f48])).
% 0.20/0.55  fof(f864,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f855,f51])).
% 0.20/0.55  fof(f855,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.55    inference(superposition,[],[f65,f602])).
% 0.20/0.55  fof(f602,plain,(
% 0.20/0.55    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.55    inference(superposition,[],[f321,f155])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    k9_relat_1(sK2,sK0) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.20/0.55    inference(resolution,[],[f79,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f321,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f320,f47])).
% 0.20/0.55  fof(f320,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f319,f48])).
% 0.20/0.55  fof(f319,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.55    inference(resolution,[],[f82,f51])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f75,f76,f76])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f72,f77])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f271,plain,(
% 0.20/0.55    spl3_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f270])).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    $false | spl3_8),
% 0.20/0.55    inference(subsumption_resolution,[],[f269,f47])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | spl3_8),
% 0.20/0.55    inference(subsumption_resolution,[],[f268,f48])).
% 0.20/0.55  fof(f268,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_8),
% 0.20/0.55    inference(resolution,[],[f247,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl3_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f245])).
% 0.20/0.55  fof(f263,plain,(
% 0.20/0.55    spl3_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.55  fof(f262,plain,(
% 0.20/0.55    $false | spl3_7),
% 0.20/0.55    inference(subsumption_resolution,[],[f261,f47])).
% 0.20/0.55  fof(f261,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | spl3_7),
% 0.20/0.55    inference(subsumption_resolution,[],[f260,f48])).
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_7),
% 0.20/0.55    inference(resolution,[],[f243,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    ~v1_relat_1(k2_funct_1(sK2)) | spl3_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f241])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    ~spl3_7 | spl3_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f239,f257,f241])).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.20/0.55    inference(superposition,[],[f61,f237])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (23201)------------------------------
% 0.20/0.55  % (23201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23201)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (23201)Memory used [KB]: 11257
% 0.20/0.55  % (23201)Time elapsed: 0.099 s
% 0.20/0.55  % (23201)------------------------------
% 0.20/0.55  % (23201)------------------------------
% 0.20/0.55  % (23208)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.55  % (23194)Success in time 0.195 s
%------------------------------------------------------------------------------
