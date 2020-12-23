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
% DateTime   : Thu Dec  3 12:54:37 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 148 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  272 ( 595 expanded)
%              Number of equality atoms :   47 ( 114 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(resolution,[],[f155,f112])).

fof(f112,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f52,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f110,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f96,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f50,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f155,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f90])).

fof(f90,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f48,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f146,f51])).

fof(f51,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f138,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f138,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1),X0)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f117,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f88,f113])).

fof(f113,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) ),
    inference(superposition,[],[f92,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f92,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f91,f48])).

fof(f91,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f49,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (25240)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (25242)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25241)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (25266)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (25249)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (25245)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (25262)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (25248)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (25243)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (25255)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (25254)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (25244)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (25250)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (25267)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (25250)Refutation not found, incomplete strategy% (25250)------------------------------
% 0.21/0.55  % (25250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25250)Memory used [KB]: 10746
% 0.21/0.55  % (25250)Time elapsed: 0.135 s
% 0.21/0.55  % (25250)------------------------------
% 0.21/0.55  % (25250)------------------------------
% 0.21/0.55  % (25262)Refutation not found, incomplete strategy% (25262)------------------------------
% 0.21/0.55  % (25262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25262)Memory used [KB]: 10746
% 0.21/0.55  % (25262)Time elapsed: 0.097 s
% 0.21/0.55  % (25262)------------------------------
% 0.21/0.55  % (25262)------------------------------
% 0.21/0.55  % (25265)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (25251)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (25259)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (25258)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (25261)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (25260)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (25252)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (25253)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (25268)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.54/0.56  % (25269)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.54/0.56  % (25246)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.54/0.56  % (25257)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.56  % (25256)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % (25257)Refutation not found, incomplete strategy% (25257)------------------------------
% 1.54/0.57  % (25257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (25257)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (25257)Memory used [KB]: 10618
% 1.54/0.57  % (25257)Time elapsed: 0.154 s
% 1.54/0.57  % (25257)------------------------------
% 1.54/0.57  % (25257)------------------------------
% 1.54/0.57  % (25248)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f217,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(resolution,[],[f155,f112])).
% 1.54/0.57  fof(f112,plain,(
% 1.54/0.57    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.54/0.57    inference(subsumption_resolution,[],[f110,f52])).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.57    inference(flattening,[],[f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.54/0.57    inference(negated_conjecture,[],[f18])).
% 1.54/0.57  fof(f18,conjecture,(
% 1.54/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.54/0.57  fof(f110,plain,(
% 1.54/0.57    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.54/0.57    inference(resolution,[],[f96,f65])).
% 1.54/0.57  fof(f65,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.57    inference(flattening,[],[f37])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.57    inference(nnf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.57  fof(f96,plain,(
% 1.54/0.57    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f93,f48])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    v1_relat_1(sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f93,plain,(
% 1.54/0.57    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.54/0.57    inference(resolution,[],[f50,f59])).
% 1.54/0.57  fof(f59,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(flattening,[],[f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,axiom,(
% 1.54/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f155,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f154,f48])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f153,f49])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    v1_funct_1(sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f153,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f152,f90])).
% 1.54/0.57  fof(f90,plain,(
% 1.54/0.57    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 1.54/0.57    inference(resolution,[],[f48,f58])).
% 1.54/0.57  fof(f58,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,axiom,(
% 1.54/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.54/0.57  fof(f152,plain,(
% 1.54/0.57    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f146,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    v2_funct_1(sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f36])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    ( ! [X0] : (~v2_funct_1(sK1) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.57    inference(resolution,[],[f138,f71])).
% 1.54/0.57  fof(f71,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.54/0.57  fof(f138,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f131])).
% 1.54/0.57  fof(f131,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.54/0.57    inference(resolution,[],[f120,f68])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f42])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(rectify,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(nnf_transformation,[],[f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.57  fof(f120,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1),X0) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X1)) )),
% 1.54/0.57    inference(resolution,[],[f117,f67])).
% 1.54/0.57  fof(f67,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f42])).
% 1.54/0.57  fof(f117,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) | r2_hidden(X1,X0)) )),
% 1.54/0.57    inference(superposition,[],[f88,f113])).
% 1.54/0.57  fof(f113,plain,(
% 1.54/0.57    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))) )),
% 1.54/0.57    inference(superposition,[],[f92,f82])).
% 1.54/0.57  fof(f82,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f57,f81])).
% 1.54/0.57  fof(f81,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f55,f80])).
% 1.54/0.57  fof(f80,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f56,f79])).
% 1.54/0.57  fof(f79,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f69,f78])).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.57  fof(f92,plain,(
% 1.54/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f91,f48])).
% 1.54/0.57  fof(f91,plain,(
% 1.54/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~v1_relat_1(sK1)) )),
% 1.54/0.57    inference(resolution,[],[f49,f83])).
% 1.54/0.57  fof(f83,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f61,f81])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(flattening,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,axiom,(
% 1.54/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.54/0.57  fof(f88,plain,(
% 1.54/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.54/0.57    inference(equality_resolution,[],[f72])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.54/0.57    inference(rectify,[],[f44])).
% 1.54/0.57  fof(f44,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.54/0.57    inference(flattening,[],[f43])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.54/0.57    inference(nnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (25248)------------------------------
% 1.54/0.57  % (25248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (25248)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (25248)Memory used [KB]: 10874
% 1.54/0.57  % (25248)Time elapsed: 0.161 s
% 1.54/0.57  % (25248)------------------------------
% 1.54/0.57  % (25248)------------------------------
% 1.54/0.57  % (25263)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  % (25239)Success in time 0.211 s
%------------------------------------------------------------------------------
