%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t17_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  36 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 139 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f11])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
    & v1_finset_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k9_relat_1(X1,X0))
        & v1_finset_1(X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
      & v1_finset_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v1_finset_1(X0)
         => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t17_finset_1.p',t17_finset_1)).

fof(f18,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f17,f12])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f16,f13])).

fof(f13,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f15,f14])).

fof(f14,plain,(
    ~ v1_finset_1(k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t17_finset_1.p',fc13_finset_1)).
%------------------------------------------------------------------------------
