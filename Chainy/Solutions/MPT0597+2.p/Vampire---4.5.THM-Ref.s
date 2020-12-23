%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0597+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   19 (  43 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 159 expanded)
%              Number of equality atoms :   26 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2875,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2874,f1655])).

fof(f1655,plain,(
    v1_relat_1(sK54) ),
    inference(cnf_transformation,[],[f1348])).

fof(f1348,plain,
    ( k9_relat_1(sK54,sK53) != k9_relat_1(sK55,sK53)
    & k7_relat_1(sK54,sK53) = k7_relat_1(sK55,sK53)
    & v1_relat_1(sK55)
    & v1_relat_1(sK54) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK53,sK54,sK55])],[f867,f1347,f1346])).

fof(f1346,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
            & k7_relat_1(X2,X0) = k7_relat_1(X1,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k9_relat_1(sK54,sK53) != k9_relat_1(X2,sK53)
          & k7_relat_1(X2,sK53) = k7_relat_1(sK54,sK53)
          & v1_relat_1(X2) )
      & v1_relat_1(sK54) ) ),
    introduced(choice_axiom,[])).

fof(f1347,plain,
    ( ? [X2] :
        ( k9_relat_1(sK54,sK53) != k9_relat_1(X2,sK53)
        & k7_relat_1(X2,sK53) = k7_relat_1(sK54,sK53)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK54,sK53) != k9_relat_1(sK55,sK53)
      & k7_relat_1(sK54,sK53) = k7_relat_1(sK55,sK53)
      & v1_relat_1(sK55) ) ),
    introduced(choice_axiom,[])).

fof(f867,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X2,X0) = k7_relat_1(X1,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f866])).

fof(f866,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X2,X0) = k7_relat_1(X1,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f795])).

fof(f795,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( k7_relat_1(X2,X0) = k7_relat_1(X1,X0)
             => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f794])).

fof(f794,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X2,X0) = k7_relat_1(X1,X0)
           => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

fof(f2874,plain,(
    ~ v1_relat_1(sK54) ),
    inference(subsumption_resolution,[],[f2837,f1658])).

fof(f1658,plain,(
    k9_relat_1(sK54,sK53) != k9_relat_1(sK55,sK53) ),
    inference(cnf_transformation,[],[f1348])).

fof(f2837,plain,
    ( k9_relat_1(sK54,sK53) = k9_relat_1(sK55,sK53)
    | ~ v1_relat_1(sK54) ),
    inference(superposition,[],[f2675,f1678])).

fof(f1678,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f884])).

fof(f884,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f739,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2675,plain,(
    k9_relat_1(sK55,sK53) = k2_relat_1(k7_relat_1(sK54,sK53)) ),
    inference(subsumption_resolution,[],[f2628,f1656])).

fof(f1656,plain,(
    v1_relat_1(sK55) ),
    inference(cnf_transformation,[],[f1348])).

fof(f2628,plain,
    ( k9_relat_1(sK55,sK53) = k2_relat_1(k7_relat_1(sK54,sK53))
    | ~ v1_relat_1(sK55) ),
    inference(superposition,[],[f1678,f1657])).

fof(f1657,plain,(
    k7_relat_1(sK54,sK53) = k7_relat_1(sK55,sK53) ),
    inference(cnf_transformation,[],[f1348])).
%------------------------------------------------------------------------------
