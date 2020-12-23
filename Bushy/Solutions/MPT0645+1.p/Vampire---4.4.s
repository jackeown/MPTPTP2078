%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t52_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    $false ),
    inference(resolution,[],[f14,f13])).

fof(f13,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f11,plain,
    ( ? [X0] : ~ v2_funct_1(k6_relat_1(X0))
   => ~ v2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t52_funct_1.p',t52_funct_1)).

fof(f14,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t52_funct_1.p',fc4_funct_1)).
%------------------------------------------------------------------------------
