%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0540+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 4.38s
% Output     : Refutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   47 (  97 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 254 expanded)
%              Number of equality atoms :   62 ( 126 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10086,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10085,f2153])).

fof(f2153,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f2152])).

fof(f2152,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1552])).

fof(f1552,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1222,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK19(X0,X1) != X0
            | ~ r2_hidden(sK19(X0,X1),X1) )
          & ( sK19(X0,X1) = X0
            | r2_hidden(sK19(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f1220,f1221])).

fof(f1221,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK19(X0,X1) != X0
          | ~ r2_hidden(sK19(X0,X1),X1) )
        & ( sK19(X0,X1) = X0
          | r2_hidden(sK19(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1220,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1219])).

fof(f1219,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f10085,plain,(
    ~ r2_hidden(k7_relat_1(k8_relat_1(sK0,sK2),sK1),k1_tarski(k7_relat_1(k8_relat_1(sK0,sK2),sK1))) ),
    inference(forward_demodulation,[],[f10073,f3822])).

fof(f3822,plain,(
    ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1) ),
    inference(forward_demodulation,[],[f3821,f2669])).

fof(f2669,plain,(
    ! [X0] : k5_relat_1(sK2,k6_relat_1(X0)) = k8_relat_1(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f1369,f1438])).

fof(f1438,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f859])).

fof(f859,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f699,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f1369,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1150])).

fof(f1150,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f793,f1149])).

fof(f1149,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f793,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f718,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f717])).

fof(f717,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f3821,plain,(
    ! [X0,X1] : k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f2398,f3807])).

fof(f3807,plain,(
    ! [X0,X1] : k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k8_relat_1(X1,k7_relat_1(sK2,X0)) ),
    inference(backward_demodulation,[],[f3709,f2435])).

fof(f2435,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(unit_resulting_resolution,[],[f1369,f1396])).

fof(f1396,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f823])).

fof(f823,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f782])).

fof(f782,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f3709,plain,(
    ! [X0,X1] : k8_relat_1(X1,k5_relat_1(k6_relat_1(X0),sK2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f3673,f2627])).

fof(f2627,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(unit_resulting_resolution,[],[f1942,f1369,f1430])).

fof(f1430,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f849])).

fof(f849,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f715])).

fof(f715,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f1942,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f3673,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f3208,f2669])).

fof(f3208,plain,(
    ! [X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK2,k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f1942,f1942,f1369,f1749])).

fof(f1749,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1039])).

fof(f1039,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f753])).

fof(f753,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2398,plain,(
    ! [X0,X1] : k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k5_relat_1(k7_relat_1(sK2,X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1942,f1369,f1386])).

fof(f1386,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f812])).

fof(f812,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f690])).

fof(f690,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f10073,plain,(
    ~ r2_hidden(k7_relat_1(k8_relat_1(sK0,sK2),sK1),k1_tarski(k8_relat_1(sK0,k7_relat_1(sK2,sK1)))) ),
    inference(unit_resulting_resolution,[],[f1370,f2154])).

fof(f2154,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1551])).

fof(f1551,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1222])).

fof(f1370,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1150])).
%------------------------------------------------------------------------------
