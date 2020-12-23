%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0503+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  73 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2451,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2444,f1466])).

% (18730)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
fof(f1466,plain,(
    v1_relat_1(sK53) ),
    inference(cnf_transformation,[],[f1162])).

fof(f1162,plain,
    ( k7_relat_1(sK53,sK52) != k7_relat_1(k7_relat_1(sK53,sK52),sK52)
    & v1_relat_1(sK53) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK52,sK53])],[f752,f1161])).

fof(f1161,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK53,sK52) != k7_relat_1(k7_relat_1(sK53,sK52),sK52)
      & v1_relat_1(sK53) ) ),
    introduced(choice_axiom,[])).

fof(f752,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f676])).

fof(f676,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f675])).

fof(f675,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(f2444,plain,(
    ~ v1_relat_1(sK53) ),
    inference(resolution,[],[f2436,f1490])).

fof(f1490,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f771])).

fof(f771,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2436,plain,(
    ~ v1_relat_1(k7_relat_1(sK53,sK52)) ),
    inference(subsumption_resolution,[],[f2426,f1466])).

fof(f2426,plain,
    ( ~ v1_relat_1(k7_relat_1(sK53,sK52))
    | ~ v1_relat_1(sK53) ),
    inference(resolution,[],[f2380,f1488])).

fof(f1488,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f769])).

fof(f769,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f2380,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK53,sK52)),sK52)
    | ~ v1_relat_1(k7_relat_1(sK53,sK52)) ),
    inference(trivial_inequality_removal,[],[f2378])).

fof(f2378,plain,
    ( k7_relat_1(sK53,sK52) != k7_relat_1(sK53,sK52)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK53,sK52)),sK52)
    | ~ v1_relat_1(k7_relat_1(sK53,sK52)) ),
    inference(superposition,[],[f1467,f1481])).

fof(f1481,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f761])).

fof(f761,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f760])).

fof(f760,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f744])).

fof(f744,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f1467,plain,(
    k7_relat_1(sK53,sK52) != k7_relat_1(k7_relat_1(sK53,sK52),sK52) ),
    inference(cnf_transformation,[],[f1162])).
%------------------------------------------------------------------------------
