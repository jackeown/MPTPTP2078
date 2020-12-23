%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0487+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   36 (  93 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  131 ( 629 expanded)
%              Number of equality atoms :   54 ( 285 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3740,f1415])).

fof(f1415,plain,(
    v1_relat_1(sK48) ),
    inference(cnf_transformation,[],[f1126])).

fof(f1126,plain,
    ( sK48 != sK50
    & k6_relat_1(sK47) = k5_relat_1(sK49,sK50)
    & k5_relat_1(sK48,sK49) = k6_relat_1(k1_relat_1(sK50))
    & r1_tarski(k2_relat_1(sK48),sK47)
    & v1_relat_1(sK50)
    & v1_relat_1(sK49)
    & v1_relat_1(sK48) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK47,sK48,sK49,sK50])],[f734,f1125,f1124,f1123])).

fof(f1123,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X1 != X3
                & k6_relat_1(X0) = k5_relat_1(X2,X3)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                & r1_tarski(k2_relat_1(X1),X0)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK48 != X3
              & k5_relat_1(X2,X3) = k6_relat_1(sK47)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK48,X2)
              & r1_tarski(k2_relat_1(sK48),sK47)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK48) ) ),
    introduced(choice_axiom,[])).

fof(f1124,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK48 != X3
            & k5_relat_1(X2,X3) = k6_relat_1(sK47)
            & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK48,X2)
            & r1_tarski(k2_relat_1(sK48),sK47)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK48 != X3
          & k6_relat_1(sK47) = k5_relat_1(sK49,X3)
          & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK48,sK49)
          & r1_tarski(k2_relat_1(sK48),sK47)
          & v1_relat_1(X3) )
      & v1_relat_1(sK49) ) ),
    introduced(choice_axiom,[])).

fof(f1125,plain,
    ( ? [X3] :
        ( sK48 != X3
        & k6_relat_1(sK47) = k5_relat_1(sK49,X3)
        & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK48,sK49)
        & r1_tarski(k2_relat_1(sK48),sK47)
        & v1_relat_1(X3) )
   => ( sK48 != sK50
      & k6_relat_1(sK47) = k5_relat_1(sK49,sK50)
      & k5_relat_1(sK48,sK49) = k6_relat_1(k1_relat_1(sK50))
      & r1_tarski(k2_relat_1(sK48),sK47)
      & v1_relat_1(sK50) ) ),
    introduced(choice_axiom,[])).

fof(f734,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f733])).

fof(f733,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f727])).

fof(f727,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f726])).

fof(f726,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).

fof(f3740,plain,(
    ~ v1_relat_1(sK48) ),
    inference(subsumption_resolution,[],[f3739,f1418])).

fof(f1418,plain,(
    r1_tarski(k2_relat_1(sK48),sK47) ),
    inference(cnf_transformation,[],[f1126])).

fof(f3739,plain,
    ( ~ r1_tarski(k2_relat_1(sK48),sK47)
    | ~ v1_relat_1(sK48) ),
    inference(subsumption_resolution,[],[f3707,f1421])).

fof(f1421,plain,(
    sK48 != sK50 ),
    inference(cnf_transformation,[],[f1126])).

fof(f3707,plain,
    ( sK48 = sK50
    | ~ r1_tarski(k2_relat_1(sK48),sK47)
    | ~ v1_relat_1(sK48) ),
    inference(superposition,[],[f3642,f1447])).

fof(f1447,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f742])).

fof(f742,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f723,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f3642,plain,(
    sK50 = k5_relat_1(sK48,k6_relat_1(sK47)) ),
    inference(forward_demodulation,[],[f3641,f1420])).

fof(f1420,plain,(
    k6_relat_1(sK47) = k5_relat_1(sK49,sK50) ),
    inference(cnf_transformation,[],[f1126])).

fof(f3641,plain,(
    sK50 = k5_relat_1(sK48,k5_relat_1(sK49,sK50)) ),
    inference(subsumption_resolution,[],[f3634,f1417])).

fof(f1417,plain,(
    v1_relat_1(sK50) ),
    inference(cnf_transformation,[],[f1126])).

fof(f3634,plain,
    ( sK50 = k5_relat_1(sK48,k5_relat_1(sK49,sK50))
    | ~ v1_relat_1(sK50) ),
    inference(duplicate_literal_removal,[],[f3565])).

fof(f3565,plain,
    ( sK50 = k5_relat_1(sK48,k5_relat_1(sK49,sK50))
    | ~ v1_relat_1(sK50)
    | ~ v1_relat_1(sK50) ),
    inference(superposition,[],[f2499,f1450])).

fof(f1450,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f745])).

fof(f745,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f722])).

fof(f722,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2499,plain,(
    ! [X11] :
      ( k5_relat_1(sK48,k5_relat_1(sK49,X11)) = k5_relat_1(k6_relat_1(k1_relat_1(sK50)),X11)
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f2498,f1415])).

fof(f2498,plain,(
    ! [X11] :
      ( k5_relat_1(sK48,k5_relat_1(sK49,X11)) = k5_relat_1(k6_relat_1(k1_relat_1(sK50)),X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(sK48) ) ),
    inference(subsumption_resolution,[],[f2463,f1416])).

fof(f1416,plain,(
    v1_relat_1(sK49) ),
    inference(cnf_transformation,[],[f1126])).

fof(f2463,plain,(
    ! [X11] :
      ( k5_relat_1(sK48,k5_relat_1(sK49,X11)) = k5_relat_1(k6_relat_1(k1_relat_1(sK50)),X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(sK49)
      | ~ v1_relat_1(sK48) ) ),
    inference(superposition,[],[f1509,f1419])).

fof(f1419,plain,(
    k5_relat_1(sK48,sK49) = k6_relat_1(k1_relat_1(sK50)) ),
    inference(cnf_transformation,[],[f1126])).

fof(f1509,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f791])).

fof(f791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f706,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
