%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0648+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   28 (  62 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :   15
%              Number of atoms          :   90 ( 273 expanded)
%              Number of equality atoms :   39 ( 113 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3492,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3491,f2110])).

fof(f2110,plain,(
    v1_relat_1(sK97) ),
    inference(cnf_transformation,[],[f1653])).

fof(f1653,plain,
    ( ( k1_relat_1(sK97) != k2_relat_1(k2_funct_1(sK97))
      | k2_relat_1(sK97) != k1_relat_1(k2_funct_1(sK97)) )
    & v2_funct_1(sK97)
    & v1_funct_1(sK97)
    & v1_relat_1(sK97) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97])],[f958,f1652])).

fof(f1652,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
          | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK97) != k2_relat_1(k2_funct_1(sK97))
        | k2_relat_1(sK97) != k1_relat_1(k2_funct_1(sK97)) )
      & v2_funct_1(sK97)
      & v1_funct_1(sK97)
      & v1_relat_1(sK97) ) ),
    introduced(choice_axiom,[])).

fof(f958,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f957])).

fof(f957,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f948])).

fof(f948,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
            & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f947])).

fof(f947,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f3491,plain,(
    ~ v1_relat_1(sK97) ),
    inference(trivial_inequality_removal,[],[f3485])).

fof(f3485,plain,
    ( k2_relat_1(sK97) != k2_relat_1(sK97)
    | ~ v1_relat_1(sK97) ),
    inference(superposition,[],[f3479,f2545])).

fof(f2545,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1197])).

fof(f1197,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f838,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f3479,plain,(
    k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97)) ),
    inference(subsumption_resolution,[],[f3478,f2110])).

fof(f3478,plain,
    ( k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97))
    | ~ v1_relat_1(sK97) ),
    inference(trivial_inequality_removal,[],[f3473])).

fof(f3473,plain,
    ( k1_relat_1(sK97) != k1_relat_1(sK97)
    | k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97))
    | ~ v1_relat_1(sK97) ),
    inference(superposition,[],[f3471,f2546])).

fof(f2546,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1197])).

fof(f3471,plain,
    ( k1_relat_1(sK97) != k2_relat_1(k4_relat_1(sK97))
    | k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97)) ),
    inference(subsumption_resolution,[],[f3470,f2110])).

fof(f3470,plain,
    ( k1_relat_1(sK97) != k2_relat_1(k4_relat_1(sK97))
    | k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97))
    | ~ v1_relat_1(sK97) ),
    inference(subsumption_resolution,[],[f3469,f2111])).

fof(f2111,plain,(
    v1_funct_1(sK97) ),
    inference(cnf_transformation,[],[f1653])).

fof(f3469,plain,
    ( k1_relat_1(sK97) != k2_relat_1(k4_relat_1(sK97))
    | k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97))
    | ~ v1_funct_1(sK97)
    | ~ v1_relat_1(sK97) ),
    inference(subsumption_resolution,[],[f3463,f2112])).

fof(f2112,plain,(
    v2_funct_1(sK97) ),
    inference(cnf_transformation,[],[f1653])).

fof(f3463,plain,
    ( k1_relat_1(sK97) != k2_relat_1(k4_relat_1(sK97))
    | k2_relat_1(sK97) != k1_relat_1(k4_relat_1(sK97))
    | ~ v2_funct_1(sK97)
    | ~ v1_funct_1(sK97)
    | ~ v1_relat_1(sK97) ),
    inference(superposition,[],[f2113,f2145])).

fof(f2145,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f977])).

fof(f977,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f976])).

fof(f976,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f2113,plain,
    ( k1_relat_1(sK97) != k2_relat_1(k2_funct_1(sK97))
    | k2_relat_1(sK97) != k1_relat_1(k2_funct_1(sK97)) ),
    inference(cnf_transformation,[],[f1653])).
%------------------------------------------------------------------------------
