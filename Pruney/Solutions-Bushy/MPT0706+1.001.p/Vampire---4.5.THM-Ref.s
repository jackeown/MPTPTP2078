%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0706+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:30 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   35 (  98 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 515 expanded)
%              Number of equality atoms :   24 ( 148 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f57])).

fof(f57,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f56,f18])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & r1_tarski(sK1,k2_relat_1(sK2))
    & r1_tarski(sK0,k2_relat_1(sK2))
    & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK0 != sK1
      & r1_tarski(sK1,k2_relat_1(sK2))
      & r1_tarski(sK0,k2_relat_1(sK2))
      & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

fof(f56,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f54,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f54,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f50,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f49,f14])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f17,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | ~ r1_tarski(sK1,k2_relat_1(sK2))
      | r1_tarski(sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f22,f15])).

fof(f15,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f60,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f16])).

fof(f16,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f53,f23])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f52,f13])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f48,f14])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f22,f15])).

%------------------------------------------------------------------------------
