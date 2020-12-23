%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1092+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:06 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   21 (  46 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 171 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3853,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3852,f2312])).

fof(f2312,plain,(
    ~ v1_finset_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f2058])).

fof(f2058,plain,
    ( ~ v1_finset_1(k2_relat_1(sK0))
    & v1_finset_1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1744,f2057])).

fof(f2057,plain,
    ( ? [X0] :
        ( ~ v1_finset_1(k2_relat_1(X0))
        & v1_finset_1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v1_finset_1(k2_relat_1(sK0))
      & v1_finset_1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1744,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1743])).

fof(f1743,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1740])).

fof(f1740,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
         => v1_finset_1(k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1739])).

fof(f1739,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

fof(f3852,plain,(
    v1_finset_1(k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f3817,f3360])).

fof(f3360,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f2309,f2674])).

fof(f2674,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1987])).

fof(f1987,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f748])).

fof(f748,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f2309,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f2058])).

fof(f3817,plain,(
    v1_finset_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f2309,f2310,f2311,f2359])).

fof(f2359,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1783])).

fof(f1783,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1782])).

fof(f1782,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1719])).

fof(f1719,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f2311,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f2058])).

fof(f2310,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f2058])).
%------------------------------------------------------------------------------
