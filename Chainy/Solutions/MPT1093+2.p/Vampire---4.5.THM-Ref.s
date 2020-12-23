%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1093+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:06 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   43 (  95 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 416 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4365,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4357,f1953])).

fof(f1953,plain,(
    v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1881])).

fof(f1881,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1745,f1880])).

fof(f1880,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1745,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1744])).

fof(f1744,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1741])).

fof(f1741,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1740])).

fof(f1740,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_finset_1)).

fof(f4357,plain,(
    ~ v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f4318,f2246])).

fof(f2246,plain,(
    ! [X0] :
      ( v1_finset_1(k9_relat_1(sK1,X0))
      | ~ v1_finset_1(X0) ) ),
    inference(subsumption_resolution,[],[f2175,f1951])).

fof(f1951,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1881])).

fof(f2175,plain,(
    ! [X0] :
      ( v1_finset_1(k9_relat_1(sK1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f1950,f1958])).

fof(f1958,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1749])).

fof(f1749,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1748])).

fof(f1748,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1735])).

fof(f1735,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

fof(f1950,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1881])).

fof(f4318,plain,(
    ~ v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f3651,f2300])).

fof(f2300,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,X2)
      | ~ v1_finset_1(X2) ) ),
    inference(resolution,[],[f1954,f1957])).

fof(f1957,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1747])).

fof(f1747,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1746])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1731])).

fof(f1731,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f1954,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1881])).

fof(f3651,plain,(
    r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f3650,f1950])).

fof(f3650,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f3631,f2199])).

fof(f2199,plain,(
    ! [X42] : r1_tarski(k10_relat_1(sK1,X42),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1950,f2014])).

fof(f2014,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1817])).

fof(f1817,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f769])).

fof(f769,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f3631,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f2335,f2011])).

fof(f2011,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1814])).

fof(f1814,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1813])).

fof(f1813,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f965,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2335,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,X2))
      | r1_tarski(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f2334,f1950])).

fof(f2334,plain,(
    ! [X2] :
      ( r1_tarski(sK0,X2)
      | ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,X2))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f2312,f1951])).

fof(f2312,plain,(
    ! [X2] :
      ( r1_tarski(sK0,X2)
      | ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,X2))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1952,f1980])).

fof(f1980,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1772])).

fof(f1772,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1771])).

fof(f1771,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f978])).

fof(f978,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f1952,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1881])).
%------------------------------------------------------------------------------
