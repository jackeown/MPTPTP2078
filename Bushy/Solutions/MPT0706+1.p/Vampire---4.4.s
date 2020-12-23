%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t161_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  96 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 511 expanded)
%              Number of equality atoms :   23 ( 147 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(global_subsumption,[],[f44,f47])).

fof(f47,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f42,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',d10_xboole_0)).

fof(f42,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f38,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & r1_tarski(sK1,k2_relat_1(sK2))
    & r1_tarski(sK0,k2_relat_1(sK2))
    & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',t161_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f37,f20])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | r1_tarski(sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f35,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,X0))
      | ~ r1_tarski(sK1,k2_relat_1(sK2))
      | r1_tarski(sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f25,f21])).

fof(f21,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',t158_funct_1)).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f29,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))
      | ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f25,f21])).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
