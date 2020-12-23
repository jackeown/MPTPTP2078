%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 404 expanded)
%              Number of leaves         :   10 (  96 expanded)
%              Depth                    :   27
%              Number of atoms          :  247 (1750 expanded)
%              Number of equality atoms :   66 ( 366 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(subsumption_resolution,[],[f386,f33])).

fof(f33,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25])).

fof(f25,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f386,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f382,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f382,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f381,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f381,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f380,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f380,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f370,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f370,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f369,f29])).

fof(f369,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f368,f30])).

fof(f368,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f288,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f288,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(forward_demodulation,[],[f287,f64])).

fof(f64,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f63,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f287,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(forward_demodulation,[],[f286,f72])).

fof(f72,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f71,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f39,f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f286,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f40,f245])).

fof(f245,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f243,f93])).

fof(f93,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f91,f80])).

fof(f80,plain,(
    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) ),
    inference(resolution,[],[f79,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f79,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f68,f77])).

fof(f77,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f76,f47])).

fof(f76,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f74,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f68,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f65,f35])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) ) ),
    inference(superposition,[],[f37,f64])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0))
      | k1_relat_1(sK1) = k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f52,f29])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(X1) = k10_relat_1(X1,X2)
      | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f243,plain,(
    k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f241,f72])).

fof(f241,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f240,f87])).

fof(f87,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f85,f64])).

fof(f85,plain,(
    k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f83,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f48,f30])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f34,f35])).

fof(f240,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f239,f64])).

fof(f239,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))) ),
    inference(subsumption_resolution,[],[f237,f29])).

fof(f237,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f78,f30])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f73,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (9429)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (9450)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (9426)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (9427)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9442)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (9429)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f393,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f386,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.22/0.51    inference(resolution,[],[f382,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f382,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f381,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f381,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f380,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f380,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f370,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f370,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f369,f29])).
% 0.22/0.51  fof(f369,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f368,f30])).
% 0.22/0.51  fof(f368,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f288,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~v1_relat_1(k2_funct_1(sK1))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f287,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f63,f29])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f62,f30])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f38,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f286,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f71,f29])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f30])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f39,f32])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) )),
% 0.22/0.51    inference(superposition,[],[f40,f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f243,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    k1_relat_1(sK1) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.22/0.51    inference(resolution,[],[f91,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))),
% 0.22/0.51    inference(resolution,[],[f79,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0))) )),
% 0.22/0.51    inference(superposition,[],[f53,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f34,f29])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f44,f29])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.22/0.51    inference(superposition,[],[f68,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f76,f47])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f29])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f73,f30])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(resolution,[],[f40,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f29])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f66,f30])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f65,f35])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK1)) | r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.22/0.51    inference(superposition,[],[f37,f64])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0)) | k1_relat_1(sK1) = k10_relat_1(sK1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f52,f29])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(X1) = k10_relat_1(X1,X2) | ~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))) )),
% 0.22/0.51    inference(resolution,[],[f43,f37])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) = k2_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(superposition,[],[f241,f72])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.22/0.51    inference(forward_demodulation,[],[f240,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK1)) = k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))),
% 0.22/0.51    inference(superposition,[],[f85,f64])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f83,f29])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK1)) = k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f48,f30])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))) = k1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(resolution,[],[f34,f35])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))),
% 0.22/0.51    inference(forward_demodulation,[],[f239,f64])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))))),
% 0.22/0.51    inference(subsumption_resolution,[],[f237,f29])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f78,f30])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f75,f35])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(resolution,[],[f73,f36])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (9429)------------------------------
% 0.22/0.51  % (9429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9429)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (9429)Memory used [KB]: 6396
% 0.22/0.51  % (9429)Time elapsed: 0.094 s
% 0.22/0.51  % (9429)------------------------------
% 0.22/0.51  % (9429)------------------------------
% 0.22/0.52  % (9445)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (9433)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (9432)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (9438)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (9435)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (9443)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (9439)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (9430)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (9441)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (9431)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (9447)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (9436)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (9425)Success in time 0.166 s
%------------------------------------------------------------------------------
