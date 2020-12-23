%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0790+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  33 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  84 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f19])).

fof(f19,plain,(
    k1_wellord1(sK1,sK0) != k1_wellord1(sK1,sK0) ),
    inference(superposition,[],[f12,f18])).

fof(f18,plain,(
    ! [X0] : k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f17,f10])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f17,plain,(
    ! [X0] :
      ( k1_wellord1(sK1,X0) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f16,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK1))
      | k3_relat_1(k2_wellord1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f15,f10])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(X0,k3_relat_1(sK1))
      | k3_relat_1(k2_wellord1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f14,f11])).

fof(f11,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_wellord1)).

fof(f12,plain,(
    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
