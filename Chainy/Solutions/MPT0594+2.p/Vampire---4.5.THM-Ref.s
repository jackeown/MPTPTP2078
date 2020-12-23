%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0594+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 4.68s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   21 (  65 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 323 expanded)
%              Number of equality atoms :   31 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10332,f1510])).

fof(f1510,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1269])).

fof(f1269,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f862,f1268,f1267,f1266])).

fof(f1266,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
                & k1_relat_1(X0) = k1_relat_1(X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
              & k1_relat_1(X1) = k1_relat_1(sK0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1267,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
            & k1_relat_1(X1) = k1_relat_1(sK0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
          & k1_relat_1(sK0) = k1_relat_1(sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1268,plain,
    ( ? [X2] :
        ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
        & k1_relat_1(sK0) = k1_relat_1(sK1)
        & v1_relat_1(X2) )
   => ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f862,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X0) = k1_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f861])).

fof(f861,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X0) = k1_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f789])).

fof(f789,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k1_relat_1(X0) = k1_relat_1(X1)
                 => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f788])).

fof(f788,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f10332,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f10331,f8738])).

fof(f8738,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1506,f1508,f1539])).

fof(f1539,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f893])).

fof(f893,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f771])).

fof(f771,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1508,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1269])).

fof(f1506,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1269])).

fof(f10331,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f8739,f1509])).

fof(f1509,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1269])).

fof(f8739,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1507,f1508,f1539])).

fof(f1507,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1269])).
%------------------------------------------------------------------------------
