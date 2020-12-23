%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t26_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  38 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 119 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f13])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
         => v1_finset_1(k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t26_finset_1.p',t26_finset_1)).

fof(f23,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f15,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f21,f14])).

fof(f14,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f20,f16])).

fof(f16,plain,(
    ~ v1_finset_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f18,f19])).

fof(f19,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f17,f13])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t26_finset_1.p',t146_relat_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_finset_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t26_finset_1.p',fc13_finset_1)).
%------------------------------------------------------------------------------
