%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0660+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3553,f2273])).

fof(f2273,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f3553,plain,(
    ~ v1_relat_1(k6_relat_1(sK100)) ),
    inference(subsumption_resolution,[],[f3552,f2270])).

fof(f2270,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f3552,plain,
    ( ~ v1_funct_1(k6_relat_1(sK100))
    | ~ v1_relat_1(k6_relat_1(sK100)) ),
    inference(subsumption_resolution,[],[f3551,f2274])).

fof(f2274,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f947])).

fof(f947,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f3551,plain,
    ( ~ v2_funct_1(k6_relat_1(sK100))
    | ~ v1_funct_1(k6_relat_1(sK100))
    | ~ v1_relat_1(k6_relat_1(sK100)) ),
    inference(subsumption_resolution,[],[f3549,f2509])).

fof(f2509,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f864])).

fof(f864,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f3549,plain,
    ( k6_relat_1(sK100) != k4_relat_1(k6_relat_1(sK100))
    | ~ v2_funct_1(k6_relat_1(sK100))
    | ~ v1_funct_1(k6_relat_1(sK100))
    | ~ v1_relat_1(k6_relat_1(sK100)) ),
    inference(superposition,[],[f2165,f2205])).

% (12580)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f2205,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f998])).

fof(f998,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f997])).

fof(f997,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f2165,plain,(
    k6_relat_1(sK100) != k2_funct_1(k6_relat_1(sK100)) ),
    inference(cnf_transformation,[],[f1702])).

fof(f1702,plain,(
    k6_relat_1(sK100) != k2_funct_1(k6_relat_1(sK100)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100])],[f972,f1701])).

fof(f1701,plain,
    ( ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))
   => k6_relat_1(sK100) != k2_funct_1(k6_relat_1(sK100)) ),
    introduced(choice_axiom,[])).

fof(f972,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f963])).

fof(f963,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f962])).

fof(f962,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
%------------------------------------------------------------------------------
