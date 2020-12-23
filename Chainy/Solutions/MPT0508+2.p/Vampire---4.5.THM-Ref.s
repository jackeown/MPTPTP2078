%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0508+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  68 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4023,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4022,f1739])).

fof(f1739,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f1326])).

fof(f1326,plain,
    ( ~ r1_tarski(k7_relat_1(sK5,sK3),k7_relat_1(sK6,sK4))
    & r1_tarski(sK3,sK4)
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f769,f1325,f1324])).

fof(f1324,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK5,sK3),k7_relat_1(X3,sK4))
          & r1_tarski(sK3,sK4)
          & r1_tarski(sK5,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1325,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK5,sK3),k7_relat_1(X3,sK4))
        & r1_tarski(sK3,sK4)
        & r1_tarski(sK5,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK5,sK3),k7_relat_1(sK6,sK4))
      & r1_tarski(sK3,sK4)
      & r1_tarski(sK5,sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f769,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f768])).

fof(f768,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f681])).

fof(f681,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f680])).

fof(f680,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f4022,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4021,f1736])).

fof(f1736,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1326])).

fof(f4021,plain,
    ( ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4020,f1737])).

fof(f1737,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f1326])).

fof(f4020,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(subsumption_resolution,[],[f4018,f1738])).

fof(f1738,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f1326])).

fof(f4018,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ r1_tarski(sK3,sK4) ),
    inference(resolution,[],[f2056,f4014])).

fof(f4014,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_relat_1(sK5,X0),k7_relat_1(sK6,sK4))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f4013,f1736])).

fof(f4013,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | ~ v1_relat_1(sK5)
      | ~ r1_tarski(k7_relat_1(sK5,X0),k7_relat_1(sK6,sK4)) ) ),
    inference(resolution,[],[f2410,f4001])).

fof(f4001,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_relat_1(sK5,sK3),X0)
      | ~ r1_tarski(X0,k7_relat_1(sK6,sK4)) ) ),
    inference(resolution,[],[f2484,f1740])).

fof(f1740,plain,(
    ~ r1_tarski(k7_relat_1(sK5,sK3),k7_relat_1(sK6,sK4)) ),
    inference(cnf_transformation,[],[f1326])).

fof(f2484,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1207])).

fof(f1207,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1206])).

fof(f1206,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2410,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1119])).

fof(f1119,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1118])).

fof(f1118,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f678])).

fof(f678,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f2056,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f909])).

fof(f909,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f908])).

fof(f908,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f679,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
