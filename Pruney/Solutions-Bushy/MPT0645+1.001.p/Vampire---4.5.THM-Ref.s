%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    $false ),
    inference(resolution,[],[f7,f9])).

fof(f9,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f7,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f5])).

fof(f5,plain,
    ( ? [X0] : ~ v2_funct_1(k6_relat_1(X0))
   => ~ v2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

%------------------------------------------------------------------------------
