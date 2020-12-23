%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t209_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  27 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => k7_relat_1(X1,X0) = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t209_relat_1.p',t209_relat_1)).

fof(f33,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f30,f19])).

fof(f19,plain,(
    k7_relat_1(sK1,sK0) != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,
    ( k7_relat_1(sK1,sK0) = sK1
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t209_relat_1.p',d18_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t209_relat_1.p',t97_relat_1)).
%------------------------------------------------------------------------------
